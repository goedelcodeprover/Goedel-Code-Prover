#!/usr/bin/env python3
"""
Re-select optimal decomposition results from existing iteration_logs using a new selection strategy.

Usage:
  python scripts/reselect_from_logs.py \
    --input results/iteration_logs_20260217_082305.json \
    --output results/decomposed_formal_solutions_reselected.json \
    --max_lemmas 16
"""

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path


def calculate_reduction_score(score_dict: dict) -> float:
    if not score_dict:
        return 0.0
    lemma_node_counts = [v for v in score_dict.values() if v >= 0]
    if not lemma_node_counts:
        return 0.0
    temperature = 5.0
    scaled = [nc / temperature for nc in lemma_node_counts]
    max_scaled = max(scaled)
    logsumexp = max_scaled + math.log(sum(math.exp(s - max_scaled) for s in scaled))
    return logsumexp * temperature


def count_lemmas(code: str) -> int:
    return sum(1 for line in code.splitlines()
               if line.lstrip().startswith(('lemma ', 'theorem ')))


RESULT_PRIORITY = {
    "prove_no_sorry": 0,
    "quickcheck_success": 1,
    "quickcheck_failed": 2,
    "prove_theorem_failed": 3,
    "error": 4,
}


def process_problem(problem: dict, max_lemmas: int) -> dict:
    """Process a single problem, selecting the best from all iteration intermediate states."""
    pid = problem["problem_id"]
    formal_problem = problem.get("formal_problem", "")
    attempts = problem.get("attempts", [])

    # If no attempts structure (old format for pass_k=1), use iterations field
    if not attempts and "iterations" in problem:
        attempts = [{"iterations": problem["iterations"], "result": problem.get("final_result")}]

    # Expand all iteration intermediate states as candidates
    candidates = []
    for att in attempts:
        for iter_log in att.get("iterations", []):
            result_str = iter_log.get("result")
            output_code = iter_log.get("output_code")
            output_scores = iter_log.get("output_scores")
            if result_str in ("prove_no_sorry", "quickcheck_success") and output_code:
                score = calculate_reduction_score(output_scores) if output_scores else float('inf')
                candidates.append({
                    "formal_solution": output_code,
                    "result": result_str,
                    "score": score,
                    "num_lemmas": count_lemmas(output_code),
                })

    if not candidates:
        return {
            "problem_id": pid,
            "formal_problem": formal_problem,
            "formal_solution": "",
            "_meta": {"num_candidates": 0, "result": "no_candidates", "score": float('inf'), "num_lemmas": 0},
        }

    # Select best: prove_no_sorry exempt from max_lemmas -> filter rest by max_lemmas -> result priority -> lowest score
    pool = candidates
    if max_lemmas > 0:
        proven = [c for c in pool if c["result"] == "prove_no_sorry"]
        rest = [c for c in pool if c["result"] != "prove_no_sorry" and c["num_lemmas"] <= max_lemmas]
        filtered = proven + rest
        if filtered:
            pool = filtered
        else:
            best = min(pool, key=lambda c: c["num_lemmas"])
            return {
                "problem_id": pid,
                "formal_problem": formal_problem,
                "formal_solution": best["formal_solution"],
                "_meta": {"num_candidates": len(candidates), "result": best["result"],
                          "score": best["score"], "num_lemmas": best["num_lemmas"],
                          "warning": f"all {len(candidates)} exceeded max_lemmas={max_lemmas}"},
            }

    best_priority = min(RESULT_PRIORITY.get(c["result"], 5) for c in pool)
    top_group = [c for c in pool if RESULT_PRIORITY.get(c["result"], 5) == best_priority]
    best = min(top_group, key=lambda c: c["score"])

    return {
        "problem_id": pid,
        "formal_problem": formal_problem,
        "formal_solution": best["formal_solution"],
        "_meta": {"num_candidates": len(candidates), "result": best["result"],
                  "score": best["score"], "num_lemmas": best["num_lemmas"]},
    }


def main():
    parser = argparse.ArgumentParser(description="Re-select optimal decomposition from iteration_logs")
    parser.add_argument("--input", required=True, help="iteration_logs JSON file")
    parser.add_argument("--output", required=True, help="Output file path")
    parser.add_argument("--max_lemmas", type=int, default=16, help="Max number of lemma+theorem (0=unlimited)")
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"Error: File not found: {input_path}")
        sys.exit(1)

    print(f"Input: {input_path} ({input_path.stat().st_size / 1024**3:.1f} GB)")
    print(f"max_lemmas: {args.max_lemmas}")
    print("Streaming parse...")

    import ijson

    results = []
    stats = defaultdict(int)

    with open(input_path, 'rb') as f:
        for problem in ijson.items(f, 'item'):
            pid = problem.get("problem_id", "unknown")
            result = process_problem(problem, args.max_lemmas)
            meta = result["_meta"]
            stats["total"] += 1
            stats[meta["result"]] += 1

            warning = meta.get("warning", "")
            warning_str = f" [{warning}]" if warning else ""
            print(f"  {pid}: {meta['num_candidates']} candidates -> {meta['result']} "
                  f"(score={meta['score']:.1f}, lemmas={meta['num_lemmas']}){warning_str}")

            if meta["result"] == "no_candidates":
                stats["skipped"] += 1
                continue

            results.append({
                "problem_id": result["problem_id"],
                "formal_problem": result["formal_problem"],
                "formal_solution": result["formal_solution"],
            })

    results.sort(key=lambda x: x["problem_id"])

    output_path = Path(args.output)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(results, f, ensure_ascii=False, indent=2)

    print(f"\nDone! Total {stats['total']} problems, output {len(results)}")
    print(f"  prove_no_sorry: {stats.get('prove_no_sorry', 0)}")
    print(f"  quickcheck_success: {stats.get('quickcheck_success', 0)}")
    print(f"  Skipped (no_candidates): {stats.get('skipped', 0)}")
    print(f"Output: {output_path}")


if __name__ == "__main__":
    main()
