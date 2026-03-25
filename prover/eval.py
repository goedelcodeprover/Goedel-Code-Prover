#!/usr/bin/env python3
"""
Evaluation script: compute pass@k results from the results directory

Usage:
    python eval.py <results_dir>
    python eval.py test_qwen
    python eval.py test_gemini
    python eval.py test_sft
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path


def load_results(results_dir: str) -> dict:
    """
    Load all JSON files from the results directory, grouped by problem
    
    Returns:
        {base_problem_id: [(run_idx, result_dict), ...]}
    """
    problem_runs = defaultdict(list)
    
    for filename in sorted(os.listdir(results_dir)):
        if not filename.endswith('.json'):
            continue
        
        filepath = os.path.join(results_dir, filename)
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                data = json.load(f)
        except (json.JSONDecodeError, IOError) as e:
            print(f"  Warning: skipping {filename}: {e}", file=sys.stderr)
            continue
        
        if not isinstance(data, dict):
            continue
        
        pid = data.get('problem_id', filename.replace('.json', ''))
        
        # Extract base_pid and run_idx
        # Format: "problem_XXX_run_Y" -> base="problem_XXX", run=Y
        run_match = re.match(r'^(.+)_run_(\d+)$', pid)
        if run_match:
            base_pid = run_match.group(1)
            run_idx = int(run_match.group(2))
        else:
            base_pid = pid
            run_idx = 0
        
        problem_runs[base_pid].append((run_idx, data))
    
    # Sort by run_idx
    for pid in problem_runs:
        problem_runs[pid].sort(key=lambda x: x[0])
    
    return dict(problem_runs)


def compute_stats(problem_runs: dict) -> dict:
    """Compute statistics"""
    num_problems = len(problem_runs)
    if num_problems == 0:
        return {"num_problems": 0}
    
    # Determine k (number of runs per problem, computed as max run index + 1)
    k = max(max(idx for idx, _ in runs) + 1 for runs in problem_runs.values())
    
    # pass@k: any successful run counts as pass
    pass_k_problems = []
    for pid, runs in problem_runs.items():
        if any(data.get('success') for _, data in runs):
            pass_k_problems.append(pid)
    pass_k = len(pass_k_problems)
    
    # pass@1: only look at run_0
    pass_1_problems = []
    for pid, runs in problem_runs.items():
        run_0 = [data for idx, data in runs if idx == 0]
        if run_0 and run_0[0].get('success'):
            pass_1_problems.append(pid)
    pass_1 = len(pass_1_problems)
    
    # pass@i for i in 1..k
    pass_at_i = {}
    for i in range(1, k + 1):
        count = 0
        for pid, runs in problem_runs.items():
            # At least one success in the first i runs
            first_i_runs = [data for idx, data in runs if idx < i]
            if any(data.get('success') for data in first_i_runs):
                count += 1
        pass_at_i[i] = count
    
    # Minimum attempts for each successful problem
    success_attempts = []
    for pid in pass_k_problems:
        runs = problem_runs[pid]
        for _, data in runs:
            if data.get('success'):
                success_attempts.append(data.get('attempts', 0))
                break  # Only take the first successful one
    
    # Total iterations statistics
    total_iterations = 0
    total_no_sorry = 0
    total_cheating_rejected = 0  # no_sorry but not success
    
    for pid, runs in problem_runs.items():
        for _, data in runs:
            iters = data.get('iterations', [])
            total_iterations += len(iters)
            for it in iters:
                lr = it.get('lean_result')
                if lr and isinstance(lr, dict) and lr.get('is_valid_no_sorry'):
                    total_no_sorry += 1
    
    # Cheating rejected = no_sorry but final success count
    # (rough estimate: total_no_sorry - successful run count for pass@k)
    success_runs = sum(
        sum(1 for _, data in runs if data.get('success'))
        for runs in problem_runs.values()
    )
    total_cheating_rejected = total_no_sorry - success_runs
    
    return {
        "num_problems": num_problems,
        "k": k,
        "pass_k": pass_k,
        "pass_1": pass_1,
        "pass_at_i": pass_at_i,
        "pass_k_problems": sorted(pass_k_problems),
        "total_iterations": total_iterations,
        "total_no_sorry": total_no_sorry,
        "total_cheating_rejected": max(0, total_cheating_rejected),
        "success_attempts": success_attempts,
        "success_runs": success_runs,
    }


def print_report(stats: dict, results_dir: str):
    """Print evaluation report"""
    n = stats["num_problems"]
    if n == 0:
        print("No result files found")
        return
    
    k = stats["k"]
    
    print(f"\n{'='*60}")
    print(f"  Evaluation Report: {results_dir}")
    print(f"{'='*60}")
    
    print(f"\n  Total problems:  {n}")
    print(f"  Runs per problem: {k}")
    
    # pass@k table
    print(f"\n  {'─'*40}")
    print(f"  {'Metric':<15} {'Passed':>6} {'Total':>6} {'Pass rate':>10}")
    print(f"  {'─'*40}")
    
    pass_at_i = stats["pass_at_i"]
    for i in sorted(pass_at_i.keys()):
        p = pass_at_i[i]
        pct = 100 * p / n if n else 0
        label = f"pass@{i}"
        print(f"  {label:<15} {p:>6} {n:>6} {pct:>9.1f}%")
    
    print(f"  {'─'*40}")
    
    # Detailed statistics
    print(f"\n  Iteration statistics:")
    print(f"    Total iterations:          {stats['total_iterations']:,}")
    print(f"    Found no_sorry proofs:  {stats['total_no_sorry']:,}")
    print(f"    Rejected by cheating detection:      ~{stats['total_cheating_rejected']:,}")
    print(f"    Successful runs:         {stats['success_runs']}")
    
    if stats["success_attempts"]:
        avg_attempts = sum(stats["success_attempts"]) / len(stats["success_attempts"])
        min_att = min(stats["success_attempts"])
        max_att = max(stats["success_attempts"])
        print(f"\n  Attempts for successful problems:")
        print(f"    Average: {avg_attempts:.1f}, Min: {min_att}, Max: {max_att}")
    
    passed = stats["pass_k_problems"]
    
    if passed:
        print(f"\n  pass@{k} passed problems ({len(passed)}):")
        # Display multiple per line
        line = "    "
        for i, pid in enumerate(passed):
            line += f"{pid}, "
            if (i + 1) % 8 == 0:
                print(line.rstrip(", "))
                line = "    "
        if line.strip():
            print(line.rstrip(", "))
    
    print(f"\n{'='*60}")


def main():
    parser = argparse.ArgumentParser(description="Evaluate pass@k results in the results directory")
    parser.add_argument(
        "results_dir",
        help="Directory containing result JSON files (e.g. test_qwen, test_gemini, test_sft)",
    )
    args = parser.parse_args()
    
    results_dir = args.results_dir
    if not os.path.isdir(results_dir):
        print(f"Error: directory does not exist: {results_dir}", file=sys.stderr)
        sys.exit(1)
    
    print(f"Loading {results_dir} ...")
    problem_runs = load_results(results_dir)
    print(f"Loaded {len(problem_runs)} problem results")
    
    stats = compute_stats(problem_runs)
    print_report(stats, results_dir)


if __name__ == "__main__":
    main()
