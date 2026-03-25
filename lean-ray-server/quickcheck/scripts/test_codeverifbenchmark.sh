#!/bin/bash

# Test all .lean files under CodeVerifBenchmark
#
# Usage: ./test_codeverifbenchmark.sh [-n N] [--num N]
#   -n N, --num N: only run the first N files (optional)
#
# Pass conditions:
# - Successful compile (exit code 0)
# - Or only warnings (no real errors)
# - Or quickcheck found a counter-example
# - Or quickcheck gave up (preconditions cannot be satisfied)
# - Or Quickcheck Safety Error / Float Warning (warnings, not errors)
#
# Fail conditions:
# - Real compile errors (type errors, unsolved goals, etc.)
#
# Features:
# - Concurrent execution
# - Report after all tests finish
# - Summarize failures

# Parse CLI
max_test_count=""
while [[ $# -gt 0 ]]; do
    case $1 in
        -n|--num)
            max_test_count="$2"
            shift 2
            ;;
        *)
            echo "Unknown argument: $1"
            echo "Usage: $0 [-n N] [--num N]"
            exit 1
            ;;
    esac
done

cd "$(dirname "$0")/.."

echo "Starting CodeVerifBenchmark tests..."
echo "========================================"

# Find and sort all .lean files
mapfile -t all_files < <(find Test/CodeVerifBenchmark/found_counterexample -name "*.lean" 2>/dev/null | sort)

# If -n given, take first N files only
if [ -n "$max_test_count" ]; then
    if ! [[ "$max_test_count" =~ ^[0-9]+$ ]] || [ "$max_test_count" -le 0 ]; then
        echo "Error: -n must be a positive integer"
        exit 1
    fi
    files=("${all_files[@]:0:$max_test_count}")
    echo "Limited to $max_test_count file(s) (${#all_files[@]} found total)"
else
    files=("${all_files[@]}")
fi

total=${#files[@]}
passed=0
failed=0

# Temp dir for results
temp_dir=$(mktemp -d)
trap "rm -rf $temp_dir" EXIT

# Max parallel jobs
max_jobs=8

# Run one file
test_file() {
    local file=$1
    local index=$2
    local filename=$(basename "$file")
    local result_file="$temp_dir/$index.result"
    
    # Run and capture output
    output=$(lake env lean "$file" 2>&1)
    exit_code=$?
    
    # Pass/fail
    should_pass=false
    reason=""
    
    if [ $exit_code -eq 0 ]; then
        # Exit 0: compile succeeded
        should_pass=true
        reason="Compilation succeeded"
    else
        # Counter-example counts as success
        if echo "$output" | grep -q "Found a counter-example"; then
            should_pass=true
            reason="Found counter-example (quickcheck succeeded)"
        # quickcheck gave up counts as success
        elif echo "$output" | grep -q "Gave up after failing to generate values that fulfill the preconditions"; then
            should_pass=true
            reason="quickcheck gave up (preconditions cannot be satisfied)"
        # Safety/Float warnings only
        elif echo "$output" | grep -q "\[Quickcheck Safety Error\]" || echo "$output" | grep -q "\[Quickcheck Float Warning\]"; then
            should_pass=true
            reason="Quickcheck safety warning (does not fail test)"
        # C Quickcheck all passed
        elif echo "$output" | grep -q "C Quickcheck: All tests passed!"; then
            should_pass=true
            reason="C Quickcheck: all tests passed"
        # C Quickcheck counter-example
        elif echo "$output" | grep -q "C Quickcheck found a counter-example!"; then
            should_pass=true
            reason="C Quickcheck found counter-example"
        else
            # Top-level error lines; exclude Safety/Float
            errors=$(echo "$output" | grep "^[^[:space:]].*: error:" | grep -v "Quickcheck Safety" | grep -v "Quickcheck Float" || true)
            
            if [ -z "$errors" ]; then
                # Only warnings or debug
                should_pass=true
                reason="Only warnings"
            else
                should_pass=false
                reason="Compilation error"
            fi
        fi
    fi
    
    # Persist result
    if $should_pass; then
        echo "PASS|$index|$filename|$reason" > "$result_file"
    else
        echo "FAIL|$index|$filename|$reason" > "$result_file"
        # Save output for failure report
        echo "$output" > "$result_file.output"
    fi
}

# Export for subshells
export -f test_file
export temp_dir

# Run concurrently
echo "Running tests concurrently (max $max_jobs parallel jobs)..."
echo ""

for i in "${!files[@]}"; do
    while [ $(jobs -r | wc -l) -ge $max_jobs ]; do
        sleep 0.1
    done
    
    test_file "${files[$i]}" "$i" &
done

# Wait for all background jobs
wait

echo "========================================"
echo "Tests completed, summarizing results..."
echo "========================================"
echo ""

declare -a failed_tests

# Read results in order
for i in $(seq 0 $((total - 1))); do
    result_file="$temp_dir/$i.result"
    if [ -f "$result_file" ]; then
        result=$(cat "$result_file")
        IFS='|' read -r status index filename reason <<< "$result"
        
        echo "[$((index + 1))/$total] $filename"
        
        if [ "$status" = "PASS" ]; then
            echo "  ✓ PASS ($reason)"
            passed=$((passed + 1))
        else
            echo "  ✗ FAIL ($reason)"
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
echo "========================================"

# Failure details
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

