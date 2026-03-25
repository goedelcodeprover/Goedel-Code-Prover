#!/usr/bin/env python3
"""
Profiling analysis script: Analyze prove stage logs to identify performance bottlenecks.
"""

import re
import json
import os
import sys
import asyncio
import time
from datetime import datetime, timedelta
from pathlib import Path
from collections import defaultdict

# ==================== 1. Log Timeline Analysis ====================

def parse_log_timeline(log_path: str):
    """Parse timeline from main log file"""
    entries = []
    with open(log_path, 'r', encoding='utf-8') as f:
        for line in f:
            # Parse timestamp
            match = re.match(r'(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2},\d{3})\s+-\s+(\w+)\s+-\s+(.*)', line.strip())
            if match:
                ts_str, level, msg = match.groups()
                ts = datetime.strptime(ts_str, '%Y-%m-%d %H:%M:%S,%f')
                entries.append({'timestamp': ts, 'level': level, 'message': msg})
    return entries


def analyze_timeline(entries):
    """Analyze timeline and output key metrics"""
    if not entries:
        print("No log entries found")
        return

    start_time = entries[0]['timestamp']
    last_time = entries[-1]['timestamp']
    total_duration = (last_time - start_time).total_seconds()

    print("=" * 80)
    print("                        Log Timeline Analysis")
    print("=" * 80)
    print(f"Start time: {start_time}")
    print(f"Last log:   {last_time}")
    print(f"Elapsed:    {total_duration/3600:.1f} hours")
    print()

    # Result statistics
    success_count = 0
    fail_count = 0
    result_entries = []

    for e in entries:
        msg = e['message']
        if '[Prove]' in msg and ('success' in msg or 'failed' in msg):
            is_success = 'success' in msg
            if is_success:
                success_count += 1
            else:
                fail_count += 1

            # Extract attempt count
            attempts_match = re.search(r'(\d+)\s*attempts', msg)
            attempts = int(attempts_match.group(1)) if attempts_match else 0

            # Extract problem_id
            pid_match = re.search(r'\[Prove\]\s+(\S+)', msg)
            pid = pid_match.group(1) if pid_match else "unknown"

            result_entries.append({
                'timestamp': e['timestamp'],
                'success': is_success,
                'attempts': attempts,
                'problem_id': pid,
            })

    print(f"Completed runs: {len(result_entries)} (success={success_count}, failed={fail_count})")
    print()

    # Completion gap analysis
    print("-" * 80)
    print("Key Time Gap Analysis")
    print("-" * 80)

    if len(result_entries) >= 2:
        gaps = []
        prev_ts = start_time
        for i, entry in enumerate(result_entries):
            gap = (entry['timestamp'] - prev_ts).total_seconds()
            gaps.append({
                'from': prev_ts,
                'to': entry['timestamp'],
                'gap_seconds': gap,
                'problem_id': entry['problem_id'],
                'index': i,
            })
            prev_ts = entry['timestamp']

        # Sort to find the largest gaps
        top_gaps = sorted(gaps, key=lambda x: x['gap_seconds'], reverse=True)[:10]
        print("\nTop 10 largest gaps:")
        for i, g in enumerate(top_gaps):
            gap_h = g['gap_seconds'] / 3600
            gap_m = g['gap_seconds'] / 60
            if gap_h >= 1:
                gap_str = f"{gap_h:.1f} hours"
            else:
                gap_str = f"{gap_m:.1f} minutes"
            print(f"  #{i+1}: {gap_str}  ({g['from'].strftime('%H:%M:%S')} -> {g['to'].strftime('%m-%d %H:%M:%S')})  "
                  f"after result #{g['index']} | {g['problem_id']}")

    # Throughput analysis (completions per hour)
    print("\n" + "-" * 80)
    print("Throughput Analysis (by Hour)")
    print("-" * 80)

    hour_buckets = defaultdict(int)
    for e in result_entries:
        hour_key = e['timestamp'].strftime('%m-%d %H:00')
        hour_buckets[hour_key] += 1

    for hour, count in sorted(hour_buckets.items()):
        bar = '#' * count
        print(f"  {hour}  {count:3d} runs completed  {bar}")

    # Attempt count distribution
    print("\n" + "-" * 80)
    print("Attempts Distribution")
    print("-" * 80)

    attempts_list = [e['attempts'] for e in result_entries if e['attempts'] > 0]
    if attempts_list:
        avg_attempts = sum(attempts_list) / len(attempts_list)
        min_attempts = min(attempts_list)
        max_attempts = max(attempts_list)

        # Bucketing
        buckets = defaultdict(int)
        for a in attempts_list:
            if a <= 20:
                bucket = "1-20"
            elif a <= 50:
                bucket = "21-50"
            elif a <= 100:
                bucket = "51-100"
            elif a <= 140:
                bucket = "101-140"
            else:
                bucket = "141+"
            buckets[bucket] += 1

        print(f"  Avg: {avg_attempts:.1f}, Min: {min_attempts}, Max: {max_attempts}")
        for bucket in ["1-20", "21-50", "51-100", "101-140", "141+"]:
            count = buckets.get(bucket, 0)
            bar = '#' * count
            print(f"  {bucket:>8s}: {count:3d} runs  {bar}")

    # Estimate remaining time
    print("\n" + "-" * 80)
    print("Progress & ETA")
    print("-" * 80)

    # Extract total task count from first log lines
    first_msg = entries[0]['message'] if entries else ""
    total_match = re.search(r'(\d+)\s*problems.*pass@(\d+)', entries[3]['message'] if len(entries) > 3 else "")
    if total_match:
        total_problems = int(total_match.group(1))
        pass_k = int(total_match.group(2))
        total_runs = total_problems * pass_k
        completed = len(result_entries)
        remaining = total_runs - completed

        # Estimate based on recent hour's rate
        recent_cutoff = last_time - timedelta(hours=1)
        recent_count = sum(1 for e in result_entries if e['timestamp'] > recent_cutoff)

        if recent_count > 0:
            rate_per_hour = recent_count
            eta_hours = remaining / rate_per_hour if rate_per_hour > 0 else float('inf')
            print(f"  Total tasks: {total_problems} x {pass_k} = {total_runs} runs")
            print(f"  Completed: {completed}/{total_runs} ({100*completed/total_runs:.1f}%)")
            print(f"  Remaining:  {remaining} runs")
            print(f"  Recent 1-hour rate: {rate_per_hour} runs/hour")
            print(f"  Estimated time remaining: {eta_hours:.1f} hours")
        else:
            print(f"  Total tasks: {total_runs} runs, completed: {completed}")
            print(f"  No tasks completed in the last hour!")


# ==================== 2. Code Bottleneck Analysis ====================

def analyze_code_bottlenecks():
    """Analyze performance bottlenecks in the code"""
    print("\n" + "=" * 80)
    print("                        Code Bottleneck Analysis")
    print("=" * 80)

    issues = []

    # Bottleneck 1: run_in_executor thread pool
    print("\n[CRITICAL] Bottleneck #1: asyncio default thread pool severely undersized [Severity: 5/5]")
    print("-" * 60)

    import os
    cpu_count = os.cpu_count() or 4
    default_pool_size = min(32, cpu_count + 4)

    print(f"  Current CPU cores: {cpu_count}")
    print(f"  Python default thread pool size: min(32, {cpu_count}+4) = {default_pool_size}")
    print(f"  Concurrent tasks: 189 x 10 = 1890 coroutines running simultaneously")
    print(f"  Each task's HTTP calls compete for the thread pool via run_in_executor(None, ...)")
    print()
    print(f"  PROBLEM: {1890} concurrent coroutines competing for {default_pool_size} threads")
    print(f"     -> Queuing wait dominates total time!")
    print(f"     -> Both verify_lean_code_async() and generate_proof() use run_in_executor")
    print(f"     -> Each epoch has 5+ blocking HTTP calls, all sharing the same thread pool")

    # Bottleneck 2: OpenAI client recreation
    print(f"\n[WARNING] Bottleneck #2: OpenAI client recreated on every call [Severity: 3/5]")
    print("-" * 60)
    print(f"  llm_client.py: generate_proof() calls create_client(config) every time")
    print(f"  Each call creates a new openai.OpenAI() instance = new HTTP connection pool")
    print(f"  Total LLM calls: ~1890 x 100+ = 189,000+ client creations")
    print(f"  FIX: Cache client instances, reuse HTTP connection pool")

    # Bottleneck 3: Synchronous requests library
    print(f"\n[WARNING] Bottleneck #3: Lean verification uses synchronous requests library [Severity: 4/5]")
    print("-" * 60)
    print(f"  lean_client.py uses requests.post() (synchronous blocking)")
    print(f"  Wrapped in run_in_executor, compounding the thread pool bottleneck")
    print(f"  FIX: Switch to aiohttp or httpx.AsyncClient for fully async operation")

    # Bottleneck 4: Redundant Lean verification calls
    print(f"\n[WARNING] Bottleneck #4: Redundant Lean verification calls per epoch [Severity: 3/5]")
    print("-" * 60)
    print(f"  prove_lemma() per epoch:")
    print(f"    1. Start of epoch: verify_lean_code_async (check status)")
    print(f"    2. In _try_llm_step: verify_lean_code_async (verify new code)")
    print(f"    3. After fix success: verify_lean_code_async (re-fetch goals)")
    print(f"    4. _check_and_create_success_result: check_cheating_async (another verification)")
    print(f"  Each epoch up to 5+2+1 = 8 Lean calls (including fix stage)")
    print(f"  20 epochs x 8 = up to 160 Lean calls/task")
    print(f"  FIX: Cache verification state, avoid redundant checks")

    # Bottleneck 5: max_total_attempts too high
    print(f"\n[NOTE] Bottleneck #5: max_total_attempts set too high [Severity: 2/5]")
    print("-" * 60)
    print(f"  Current config: max_total_attempts = 200000")
    print(f"  Actual upper bound: 20 epochs x 7 attempts/epoch = 140 attempts")
    print(f"  -> Not an actual bottleneck, but indicates config not carefully tuned")

    # Bottleneck 6: LLM server capacity
    print(f"\n[CRITICAL] Bottleneck #6: Limited actual LLM server capacity [Severity: 4/5]")
    print("-" * 60)
    print(f"  vLLM instances: 4-6 workers (single GPU Qwen 8B)")
    print(f"  Configured max_workers (LLM semaphore): 4096")
    print(f"  -> Semaphore is effectively useless; actual bottleneck is vLLM's request queue")
    print(f"  -> Large number of requests queue up on vLLM side, increasing overall latency")
    print(f"  SUGGESTION: Set max_workers to match vLLM's actual concurrency capacity (e.g. 24-48)")


# ==================== 3. Critical Path Estimation ====================

def estimate_critical_path():
    """Estimate critical path time for each task"""
    print("\n" + "=" * 80)
    print("                        Critical Path Estimation")
    print("=" * 80)

    # Assumed latency parameters
    lean_latency_s = 60    # Lean verification average latency (including timeout)
    llm_latency_s = 10     # LLM inference average latency (8B model)

    epochs = 20
    fix_per_epoch = 5

    # Per epoch: 1 initial verify + fix_per_epoch * (1 LLM + 1 Lean) + 1 eliminate + 1 sorry_replace
    lean_per_epoch = 1 + fix_per_epoch + 1 + 1  # = 8
    llm_per_epoch = fix_per_epoch + 1  # = 6

    total_lean = lean_per_epoch * epochs
    total_llm = llm_per_epoch * epochs

    # Serial time (no queuing)
    serial_lean_s = total_lean * lean_latency_s
    serial_llm_s = total_llm * llm_latency_s
    serial_total_s = serial_lean_s + serial_llm_s

    print(f"\n  Per task (single run) estimate:")
    print(f"    Lean calls: ~{total_lean} x {lean_latency_s}s = {serial_lean_s/60:.0f} minutes")
    print(f"    LLM calls:  ~{total_llm} x {llm_latency_s}s = {serial_llm_s/60:.0f} minutes")
    print(f"    Total serial time: ~{serial_total_s/60:.0f} minutes ({serial_total_s/3600:.1f} hours) (no queuing)")

    print(f"\n  All tasks:")
    total_runs = 1890
    print(f"    Concurrent runs: {total_runs}")
    print(f"    Ideal parallel time (no bottleneck): ~{serial_total_s/3600:.1f} hours")

    # Factor in thread pool bottleneck
    import os
    pool_size = min(32, (os.cpu_count() or 4) + 4)
    blocking_calls_total = (total_lean + total_llm) * total_runs
    effective_throughput = pool_size
    avg_call_duration = (lean_latency_s * total_lean + llm_latency_s * total_llm) / (total_lean + total_llm)

    # Simplified model: pool_size threads, each call takes avg_call_duration seconds
    total_call_seconds = blocking_calls_total * avg_call_duration
    wallclock_with_pool = total_call_seconds / pool_size

    print(f"\n  Thread pool bottleneck estimate:")
    print(f"    Total blocking HTTP calls: ~{blocking_calls_total:,}")
    print(f"    Average call duration: ~{avg_call_duration:.0f}s")
    print(f"    Thread pool size: {pool_size}")
    print(f"    Estimated wall-clock time: ~{wallclock_with_pool/3600:.0f} hours <- this is why it's slow!")

    # After optimization
    print(f"\n  Optimized estimate (using aiohttp + reasonable concurrency):")
    # Assume Lean server actual concurrency: 7 workers x 56 = 392
    # LLM server actual concurrency: 6 workers
    lean_effective = 200
    llm_effective = 24

    lean_wall = (total_lean * total_runs * lean_latency_s) / lean_effective
    llm_wall = (total_llm * total_runs * llm_latency_s) / llm_effective
    optimized_wall = max(lean_wall, llm_wall)

    print(f"    Lean wall-clock (concurrency {lean_effective}): ~{lean_wall/3600:.1f} hours")
    print(f"    LLM wall-clock (concurrency {llm_effective}):  ~{llm_wall/3600:.1f} hours")
    print(f"    Optimized estimate: ~{optimized_wall/3600:.1f} hours")
    print(f"    Speedup: ~{wallclock_with_pool/optimized_wall:.1f}x")


# ==================== 4. Real-time Performance Test ====================

async def benchmark_thread_pool():
    """Test actual throughput of the current thread pool"""
    print("\n" + "=" * 80)
    print("                        Thread Pool Throughput Benchmark")
    print("=" * 80)

    import concurrent.futures

    loop = asyncio.get_running_loop()

    # Test default thread pool
    N = 100
    SLEEP_TIME = 0.1  # Simulate a short blocking call

    def blocking_call():
        time.sleep(SLEEP_TIME)
        return True

    # Using default executor
    start = time.time()
    tasks = [loop.run_in_executor(None, blocking_call) for _ in range(N)]
    await asyncio.gather(*tasks)
    default_elapsed = time.time() - start

    import os
    default_pool_size = min(32, (os.cpu_count() or 4) + 4)
    expected_default = N * SLEEP_TIME / default_pool_size

    print(f"  Default thread pool:")
    print(f"    {N} blocking calls (each {SLEEP_TIME}s)")
    print(f"    Actual time: {default_elapsed:.2f}s (theoretical: {expected_default:.2f}s)")
    print(f"    Actual thread pool size: ~{int(N * SLEEP_TIME / default_elapsed)}")

    # Using custom large thread pool
    custom_pool = concurrent.futures.ThreadPoolExecutor(max_workers=100)
    start = time.time()
    tasks = [loop.run_in_executor(custom_pool, blocking_call) for _ in range(N)]
    await asyncio.gather(*tasks)
    custom_elapsed = time.time() - start
    custom_pool.shutdown(wait=False)

    print(f"\n  Custom thread pool (100 threads):")
    print(f"    {N} blocking calls (each {SLEEP_TIME}s)")
    print(f"    Actual time: {custom_elapsed:.2f}s")
    print(f"    Speedup: {default_elapsed/custom_elapsed:.1f}x")


# ==================== Main ====================

def main():
    log_path = sys.argv[1] if len(sys.argv) > 1 else "logs/prove_20260215_234231/main_prove_20260215_234231.log"

    if not Path(log_path).exists():
        print(f"Log file does not exist: {log_path}")
        sys.exit(1)

    # 1. Log timeline analysis
    entries = parse_log_timeline(log_path)
    analyze_timeline(entries)

    # 2. Code bottleneck analysis
    analyze_code_bottlenecks()

    # 3. Critical path estimation
    estimate_critical_path()

    # 4. Thread pool benchmark
    asyncio.run(benchmark_thread_pool())

    # Summary
    print("\n" + "=" * 80)
    print("                        Optimization Recommendations Summary")
    print("=" * 80)
    print("""
  [P0] Fix immediately:
     1. Replace requests + run_in_executor with aiohttp (lean_client.py)
     2. Replace synchronous client + run_in_executor with openai.AsyncOpenAI (llm_client.py)
     3. Cache OpenAI client instances to avoid recreating on every call

  [P1] Recommended fixes:
     4. Lower max_workers to match actual LLM concurrency capacity (e.g. 24-48)
     5. Reduce redundant Lean verification calls by caching verification state
     6. If keeping run_in_executor, set a custom large thread pool

  [P2] Long-term optimizations:
     7. Implement priority scheduling: prioritize tasks closer to success
     8. Support batch concurrency for multiple fix attempts within each epoch
""")


if __name__ == "__main__":
    main()
