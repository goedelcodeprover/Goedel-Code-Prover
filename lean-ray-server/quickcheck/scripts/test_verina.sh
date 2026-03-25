#!/bin/bash

# Test all verina_*.lean files
#
# Usage:
#   ./test_verina.sh [--subset]
#   --subset: only run files under VerinaSubset
#   default: full suite under Verina
#
# Pass conditions:
# - Successful compile (exit code 0)
# - Or only warnings (no real errors)
# - Or quickcheck found a counter-example ("Found a counter-example")
# - Or quickcheck gave up (preconditions cannot be satisfied)
# - Or Quickcheck Safety Error / Float Warning (treated as warnings, not errors)
#
# Fail conditions:
# - Real compile errors (type errors, unsolved goals, etc.)
#
# Features:
# - Run all tests concurrently
# - Report after all tests finish
# - Summarize all failures
# - Per-test timeout (default overridden by TIMEOUT_SECONDS below)

cd "$(dirname "$0")/.."

# Parse arguments
use_subset=false
if [ "$1" = "--subset" ]; then
    use_subset=true
fi

# Choose directory from arguments
if [ "$use_subset" = true ]; then
    test_dir="Test/VerinaSubset"
    version_name="VerinaSubset"
else
    test_dir="Test/Verina"
    version_name="Verina (Full Version)"
fi

echo "Starting to test verina files ($version_name)..."
echo "========================================"

# Find and sort all verina_*.lean files
mapfile -t files < <(find "$test_dir" -name "*.lean" | sort)

total=${#files[@]}
passed=0
failed=0

# Temp dir for results
temp_dir=$(mktemp -d)
trap "rm -rf $temp_dir" EXIT

# Max parallel jobs (tune to CPU cores)
max_jobs=64

# Per-test timeout (seconds); override with TIMEOUT_SECONDS
timeout_seconds=${TIMEOUT_SECONDS:-300}

# Per-test memory limit (GB); override with MEMORY_LIMIT_GB
memory_limit_gb=${MEMORY_LIMIT_GB:-32}
# Bytes for prlimit
memory_limit_bytes=$((memory_limit_gb * 1024 * 1024 * 1024))

# Run a single test file
test_file() {
    local file=$1
    local index=$2
    local filename=$(basename "$file")
    local result_file="$temp_dir/$index.result"
    
    # Start time (nanoseconds if available, else seconds)
    start_time=$(date +%s.%N 2>/dev/null || date +%s)
    
    # Run with timeout and prlimit; /usr/bin/time -v for memory stats
    # time stats go to stderr; program output to stdout/stderr — capture separately
    local output_file="$temp_dir/$index.output.tmp"
    local stderr_file="$temp_dir/$index.stderr.tmp"
    local time_file="$temp_dir/$index.time.tmp"
    
    # Split stdout, stderr, and time stats (time appends to stderr)
    /usr/bin/time -v timeout $timeout_seconds prlimit --as=$memory_limit_bytes -- lake env lean "$file" > "$output_file" 2> "$stderr_file"
    exit_code=$?
    
    # Split time stats from program stderr (stats start at "Command being timed:")
    grep -A 1000 "Command being timed:" "$stderr_file" > "$time_file" 2>/dev/null || true
    # Program stderr is everything before "Command being timed:"
    program_stderr=$(sed '/^Command being timed:/,$d' "$stderr_file" 2>/dev/null || cat "$stderr_file")
    
    # Merge stdout and stderr as combined program output
    if [ -n "$program_stderr" ]; then
        output=$(cat "$output_file" 2>/dev/null || echo "")
        output="${output}${program_stderr}"
    else
        output=$(cat "$output_file" 2>/dev/null || echo "")
    fi
    
    # Peak RSS from time -v output
    memory_kb=$(grep "Maximum resident set size (kbytes):" "$time_file" 2>/dev/null | awk '{print $6}' || echo "")
    
    # Remove temp capture files
    rm -f "$output_file" "$stderr_file" "$time_file"
    
    # Format memory for display
    if [ -n "$memory_kb" ] && [ "$memory_kb" != "0" ] && [ "$memory_kb" != "" ]; then
        # KB to MB (2 decimal places)
        memory_mb=$(echo "scale=2; $memory_kb / 1024" | bc 2>/dev/null || echo "N/A")
    else
        memory_mb="N/A"
    fi
    
    # End time and elapsed duration
    end_time=$(date +%s.%N 2>/dev/null || date +%s)
    elapsed_time=$(echo "$end_time - $start_time" | bc)
    
    # Decide pass/fail
    should_pass=false
    reason=""
    
    # timeout(1) uses exit code 124 on timeout
    if [ $exit_code -eq 124 ]; then
        should_pass=false
        reason="Timeout (exceeded ${timeout_seconds} seconds)"
    # SIGKILL from OOM/limit often yields 137 (128+9); also grep output for memory messages
    elif [ $exit_code -eq 137 ] || echo "$output" | grep -qi "out of memory\|killed\|memory limit"; then
        should_pass=false
        reason="Memory limit exceeded (exceeded ${memory_limit_gb}GB)"
    elif [ $exit_code -eq 0 ]; then
        # Exit 0: compile succeeded
        should_pass=true
        reason="Compilation succeeded"
    else
        # Counter-example found counts as success
        if echo "$output" | grep -q "Found a counter-example"; then
            should_pass=true
            reason="Found counter-example (quickcheck succeeded)"
        # quickcheck gave up also counts as success
        elif echo "$output" | grep -q "Gave up after failing to generate values that fulfill the preconditions"; then
            should_pass=true
            reason="quickcheck gave up (preconditions cannot be satisfied)"
        # Quickcheck Safety/Float warnings only — success
        elif echo "$output" | grep -q "\[Quickcheck Safety Error\]" || echo "$output" | grep -q "\[Quickcheck Float Warning\]"; then
            should_pass=true
            reason="Quickcheck safety warning (does not affect test)"
        else
            # Error lines starting at column 0 (skip indented Meta debug); exclude Safety/Float
            errors=$(echo "$output" | grep "^[^[:space:]].*: error:" | grep -v "Quickcheck Safety" | grep -v "Quickcheck Float" || true)
            
            if [ -z "$errors" ]; then
                # No real errors — only warnings or debug
                should_pass=true
                reason="Only warnings"
            else
                # Real compile errors
                should_pass=false
                reason="Compilation error"
            fi
        fi
    fi
    
    # Write result (time and memory)
    if $should_pass; then
        echo "PASS|$index|$filename|$reason|$elapsed_time|$memory_mb" > "$result_file"
    else
        echo "FAIL|$index|$filename|$reason|$elapsed_time|$memory_mb" > "$result_file"
        # Save full output for failure details
        echo "$output" > "$result_file.output"
    fi
}

# Export for subshells
export -f test_file
export temp_dir
export timeout_seconds
export memory_limit_gb
export memory_limit_bytes

# Run all tests concurrently
echo "Running tests concurrently (max $max_jobs parallel jobs)..."
echo "Memory limit per test: ${memory_limit_gb}GB"
echo "Timeout per test: ${timeout_seconds}s"
echo ""

# Wall-clock start for whole suite
total_start_time=$(date +%s.%N 2>/dev/null || date +%s)

for i in "${!files[@]}"; do
    while [ $(jobs -r | wc -l) -ge $max_jobs ]; do
        sleep 0.1
    done
    
    test_file "${files[$i]}" "$i" &
done

# Wait for all background jobs
wait

# Total elapsed time
total_end_time=$(date +%s.%N 2>/dev/null || date +%s)
total_elapsed_time=$(echo "$total_end_time - $total_start_time" | bc)

echo "========================================"
echo "Tests completed, summarizing results..."
echo "========================================"
echo ""

declare -a failed_tests
# Tests that found a counter-example
declare -a counterexample_tests
counterexample_count=0

# Read results in order
for i in $(seq 0 $((total - 1))); do
    result_file="$temp_dir/$i.result"
    if [ -f "$result_file" ]; then
        result=$(cat "$result_file")
        IFS='|' read -r status index filename reason elapsed_time memory_mb <<< "$result"
        
        # Format elapsed (2 decimals)
        formatted_time=$(printf "%.2f" "$elapsed_time" 2>/dev/null || echo "$elapsed_time")
        
        # Format memory
        if [ "$memory_mb" != "N/A" ] && [ -n "$memory_mb" ]; then
            formatted_memory=$(printf "%.2f" "$memory_mb" 2>/dev/null || echo "$memory_mb")
            memory_display="Memory: ${formatted_memory}MB"
        else
            memory_display="Memory: N/A"
        fi
        
        echo "[$((index + 1))/$total] $filename"
        
        if [ "$status" = "PASS" ]; then
            echo "  ✓ PASS ($reason) - Time: ${formatted_time}s, $memory_display"
            passed=$((passed + 1))
            # Track counter-example successes
            if [ "$reason" = "Found counter-example (quickcheck succeeded)" ]; then
                counterexample_count=$((counterexample_count + 1))
                counterexample_tests+=("$((index + 1))|$filename")
            fi
        else
            echo "  ✗ FAIL ($reason) - Time: ${formatted_time}s, $memory_display"
            failed=$((failed + 1))
            failed_tests+=("$index|$filename")
        fi
    fi
done

echo ""
echo "========================================"
echo "Test Summary"
echo "========================================"
echo "Total: $total"
echo "Passed: $passed"
echo "Failed: $failed"
echo "Success rate: $(echo "scale=1; $passed * 100 / $total" | bc)%"
formatted_total_time=$(printf "%.2f" "$total_elapsed_time" 2>/dev/null || echo "$total_elapsed_time")
echo "Total time: ${formatted_total_time}s"
echo "========================================"

# Counter-example summary
if [ $counterexample_count -gt 0 ]; then
    echo ""
    echo "========================================"
    echo "Counter-examples Found: $counterexample_count"
    echo "========================================"
    echo "Test numbers with counter-examples:"
    for counterexample_info in "${counterexample_tests[@]}"; do
        IFS='|' read -r test_num filename <<< "$counterexample_info"
        echo "  #$test_num: $filename"
    done
    echo "========================================"
fi

# Print details for failures
if [ $failed -gt 0 ]; then
    echo ""
    echo "========================================"
    echo "Failed Test Details"
    echo "========================================"
    
    for failed_info in "${failed_tests[@]}"; do
        IFS='|' read -r index filename <<< "$failed_info"
        echo ""
        echo "----------------------------------------"
        echo "[$((index + 1))/$total] $filename"
        echo "----------------------------------------"
        
        output_file="$temp_dir/$index.result.output"
        if [ -f "$output_file" ]; then
            cat "$output_file"
        fi
        echo "----------------------------------------"
    done
    
    echo ""
    echo "========================================"
    echo "$failed test(s) failed"
    echo "========================================"
    exit 1
else
    echo ""
    echo "🎉 All tests passed!"
    exit 0
fi
