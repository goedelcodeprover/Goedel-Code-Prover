#!/usr/bin/env python3
"""
Batch-test problems in a decomposed result JSON using the prover's Lean verification + cheating detection.

Only tests problems with decompose_result == "prove_no_sorry"; after verification, also runs the
prover's check_cheating (signature match + no illegal axioms); only counted as success if no sorry and no cheating.

Usage:
    python scripts/eval_decomposed_json.py results/decomposed_formal_solutions_20260228_002231.json
    python scripts/eval_decomposed_json.py results/decomposed_xxx.json --out-dir results/eval_decomposed_20260228
    python scripts/eval_decomposed_json.py results/decomposed_xxx.json --config config.yaml
"""

import argparse
import json
import os
import sys
from pathlib import Path

# Ensure prover can be imported (run from project root)
_REPO_ROOT = Path(__file__).resolve().parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))


def load_config(config_path: str = None):
    """Load config required by prover (including lean_server)."""
    from prover.config import Config, set_config

    path = str(config_path or (_REPO_ROOT / "config.yaml"))
    config = Config.from_yaml(path)
    set_config(config)
    return config


def main():
    parser = argparse.ArgumentParser(
        description="Batch-verify problems in decomposed JSON using prover verify"
    )
    parser.add_argument(
        "json_path",
        help="Decomposed result JSON path (e.g. results/decomposed_formal_solutions_xxx.json)",
    )
    parser.add_argument(
        "--out-dir",
        default=None,
        help="Output directory; if specified, writes one JSON per problem for later analysis with prover/eval.py",
    )
    parser.add_argument(
        "--config",
        default=None,
        help="Unified config file path, defaults to config.yaml in project root",
    )
    args = parser.parse_args()

    json_path = Path(args.json_path)
    if not json_path.is_file():
        print(f"Error: File not found: {json_path}", file=sys.stderr)
        sys.exit(1)

    config = load_config(args.config)
    from prover.lean_client import (
        verify_lean_code,
        check_verification_result,
        check_cheating,
    )
    from common.transform import add_evolve_block_markers

    with open(json_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list):
        print("Error: JSON should be a list of problems (array)", file=sys.stderr)
        sys.exit(1)

    # Only test problems with decompose_result == "prove_no_sorry"
    candidates = [item for item in data if item.get("decompose_result") == "prove_no_sorry"]
    total_in_file = len(data)
    total = len(candidates)
    print(f"Total problems (in file): {total_in_file}, decompose_result=prove_no_sorry: {total}")

    out_dir = Path(args.out_dir) if args.out_dir else None
    if out_dir:
        out_dir.mkdir(parents=True, exist_ok=True)

    no_sorry_ok = 0
    cheating_rejected = 0
    verify_fail = 0
    skipped = 0
    results = []

    for i, item in enumerate(candidates):
        pid = item.get("problem_id", f"item_{i}")
        formal_solution = (item.get("formal_solution") or "").strip()
        formal_problem = (item.get("formal_problem") or "").strip()

        if not formal_solution or not formal_problem:
            skipped += 1
            results.append({
                "problem_id": pid,
                "skipped": True,
                "reason": "empty_solution_or_problem",
            })
            continue

        print(f"[{i + 1}/{total}] Verifying {pid} ...", flush=True)
        raw = verify_lean_code(formal_solution, config=config)
        no_sorry, with_sorry, errors = check_verification_result(raw)

        if not no_sorry:
            verify_fail += 1
            status = "verify_fail"
            success = False
            error_message = "\n".join(errors) if errors else None
            cheating_error = None
            axioms_used = None
        else:
            # No sorry passed; now run cheating detection. Decomposed formal_solution usually lacks EVOLVE-BLOCK,
            # # passing directly to check_cheating appends verification theorems at end of file (outside namespace, causing Unknown identifier).
            # # Add EVOLVE-BLOCK markers first so the insertion point is before the last end <namespace>, staying within the namespace.
            solution_for_cheating = add_evolve_block_markers(formal_solution)
            is_cheating, cheating_error, axioms_used = check_cheating(
                solution_for_cheating, formal_problem, config
            )
            if is_cheating:
                cheating_rejected += 1
                status = "cheating_rejected"
                success = False
                error_message = cheating_error
                print(f"    → Cheating detection rejected: {cheating_error or '(no details)'}", flush=True)
                if axioms_used:
                    print(f"       axioms: {axioms_used}", flush=True)
            else:
                no_sorry_ok += 1
                status = "no_sorry_ok"
                success = True
                error_message = None
                cheating_error = None

        record = {
            "problem_id": pid,
            "success": success,
            "status": status,
            "is_valid_no_sorry": no_sorry,
            "cheating_rejected": status == "cheating_rejected",
            "error_message": error_message,
            "axioms_used": axioms_used if axioms_used else None,
        }
        results.append(record)

        if out_dir:
            safe_name = pid.replace("/", "_").replace("\\", "_").replace(" ", "_")
            if not safe_name.endswith(".json"):
                safe_name += ".json"
            out_data = {
                "problem_id": pid,
                "success": success,
                "attempts": 0,
                "remaining_sorries": 0 if success else 1,
                "error_message": record.get("error_message"),
                "iterations": [
                    {
                        "lean_result": {
                            "is_valid_no_sorry": no_sorry,
                            "is_valid_with_sorry": no_sorry or with_sorry,
                        }
                    }
                ],
            }
            with open(out_dir / safe_name, "w", encoding="utf-8") as f:
                json.dump(out_data, f, ensure_ascii=False, indent=2)

    verified = no_sorry_ok + cheating_rejected + verify_fail
    print()
    print("=" * 60)
    print("  Evaluation Summary (prove_no_sorry problems only)")
    print("=" * 60)
    print(f"  Total problems (file): {total_in_file}")
    print(f"  prove_no_sorry: {total}")
    print(f"  Skipped:          {skipped}")
    print(f"  Verified:         {verified}")
    print(f"  No sorry, no cheating: {no_sorry_ok}")
    print(f"  Cheating rejected:   {cheating_rejected}")
    print(f"  Verification failed: {verify_fail}")
    if verified:
        pct = 100 * no_sorry_ok / verified
        print(f"  Final pass rate:  {pct:.1f}%")
    if out_dir:
        print(f"\n  Results written to: {out_dir}")
        print(f"  Use prover eval to analyze: python prover/eval.py {out_dir}")
    # Summary of cheating rejection error messages
    rejected = [r for r in results if r.get("status") == "cheating_rejected"]
    if rejected:
        print(f"\n  Cheating rejection details ({len(rejected)} problems):")
        for r in rejected[:20]:  # Print at most the first 20
            msg = (r.get("error_message") or "").strip() or "(none)"
            pid = r.get("problem_id", "?")
            if len(msg) > 200:
                msg = msg[:200] + "..."
            print(f"    [{pid}] {msg}")
        if len(rejected) > 20:
            print(f"    ... {len(rejected) - 20} more problems omitted")
    print("=" * 60)


if __name__ == "__main__":
    main()
