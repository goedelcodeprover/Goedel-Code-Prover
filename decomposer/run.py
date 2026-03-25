"""
Decomposer run module — run_decompose_stage() is the entry point for the decompose stage
"""
from __future__ import annotations

import json
import logging
import threading
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, List

from tqdm import tqdm

from decomposer.config import DecomposeConfig
from decomposer.scorer import calculate_reduction_score
from decomposer.verify_single import solve_single_problem
from decomposer.utils import (
    VerifyResult,
    set_config,
    setup_logger,
    summarize_categories,
    get_usage_stats,
    BudgetExceededError,
)
from common.io_utils import save_json, load_json
from common.logger import cleanup_logger, LOG_FORMAT

logger = logging.getLogger(__name__)


def _count_lemmas(code: str) -> int:
    return sum(1 for line in code.splitlines()
               if line.lstrip().startswith(('lemma ', 'theorem ')))


_RESULT_PRIORITY = {
    VerifyResult.PROVE_NO_SORRY: 0,
    VerifyResult.CHECK_SUCCESS: 1,
    VerifyResult.CHECK_FAILED: 2,
    VerifyResult.PROVE_FAILED: 3,
    VerifyResult.ERROR: 4,
}


def _select_best(cands, max_lemmas: int):
    """Select the best result from the candidate list"""
    if max_lemmas > 0:
        proven = [c for c in cands if c[2] == VerifyResult.PROVE_NO_SORRY]
        rest = [c for c in cands if c[2] != VerifyResult.PROVE_NO_SORRY and _count_lemmas(c[1]) <= max_lemmas]
        filtered = proven + rest
        if filtered:
            cands = filtered
        else:
            logger.warning(f"  All {len(cands)} candidates exceed max_lemmas={max_lemmas}, selecting the one with fewest lemmas")
            return min(cands, key=lambda c: _count_lemmas(c[1]))

    best_priority = min(_RESULT_PRIORITY.get(c[2], 5) for c in cands)
    top_group = [c for c in cands if _RESULT_PRIORITY.get(c[2], 5) == best_priority]
    return min(top_group, key=lambda c: c[3])


def run_decompose_stage(
    benchmark_file: str,
    cfg: DecomposeConfig,
    output_dir: str,
    timestamp: str,
) -> List[Dict]:
    """
    Run the decomposition stage

    Memory optimization strategy:
    - Each run is immediately flushed to a per-run JSON file (including iteration_logs) upon completion
    - Only lightweight metadata (pid, result, score, path) is kept in memory
    - Final aggregation loads from disk on demand

    Returns:
        List of decomposition results
    """
    set_config(cfg)

    log_dir = Path(f"logs/decompose_{timestamp}")
    log_dir.mkdir(parents=True, exist_ok=True)
    results_dir = Path(output_dir) / f"decompose_runs_{timestamp}"
    results_dir.mkdir(parents=True, exist_ok=True)

    for h in logger.handlers[:]:
        if isinstance(h, logging.FileHandler):
            h.close()
            logger.removeHandler(h)
    main_log_file = log_dir / f"main_decompose_{timestamp}.log"
    main_fh = logging.FileHandler(main_log_file, encoding='utf-8')
    main_fh.setFormatter(logging.Formatter(LOG_FORMAT))
    logger.addHandler(main_fh)

    logger.info("=" * 80)
    logger.info(f"[Decompose] Starting theorem decomposition, timestamp: {timestamp}")
    logger.info("=" * 80)

    with open(benchmark_file, 'r', encoding='utf-8') as f:
        problems = json.load(f)

    pass_k = cfg.pass_k
    max_concurrent = getattr(cfg, 'max_concurrent_tasks', cfg.max_workers)
    logger.info(f"[Decompose] Loaded {len(problems)} problems")
    if pass_k > 1:
        logger.info(f"[Decompose] pass@{pass_k} mode: running {pass_k} times per problem, selecting result with lowest score")
    logger.info(f"[Decompose] max_iterations={cfg.num_iterations}, concurrency={cfg.max_workers}, max_concurrent_tasks={max_concurrent}")

    task_semaphore = threading.Semaphore(max_concurrent)

    def process_one_problem(problem, attempt_id=0):
        """Process a single problem; flush to disk immediately upon completion to free memory"""
        with task_semaphore:
            problem_id = problem.get("problem_id", "unknown")
            formal_problem = problem.get("formal_problem", "")
            logger_name = f"{problem_id}_a{attempt_id}" if pass_k > 1 else problem_id
            problem_logger = setup_logger(logger_name, str(log_dir))

            try:
                result, final_code, success_steps, result_history, iteration_logs, extra_info = solve_single_problem(
                    problem_id=problem_id,
                    formal_problem=formal_problem,
                    logger=problem_logger,
                    cfg=cfg,
                    max_iterations=cfg.num_iterations,
                )

                run_id = f"{problem_id}_a{attempt_id}" if pass_k > 1 else problem_id
                result_data = {
                    "problem_id": problem_id,
                    "result": result.value,
                    "success_steps": success_steps,
                    "result_history": result_history,
                    "formal_problem": formal_problem,
                    "formal_solution": final_code,
                    "iteration_logs": iteration_logs,
                    "extra_info": extra_info,
                }
                filepath = save_json(result_data, str(results_dir), run_id)

                return {
                    "problem_id": problem_id,
                    "result": result,
                    "success_steps": success_steps,
                    "formal_problem": formal_problem,
                    "formal_solution": final_code,
                    "extra_info": extra_info,
                    "result_path": str(filepath),
                }
            except BudgetExceededError:
                raise
            except Exception as e:
                problem_logger.error(f"Processing failed: {e}", exc_info=True)
                extra_info = {"initial_score": 0, "final_score": float('inf'), "last_error": str(e)}

                run_id = f"{problem_id}_a{attempt_id}" if pass_k > 1 else problem_id
                result_data = {
                    "problem_id": problem_id,
                    "result": VerifyResult.ERROR.value,
                    "success_steps": 0,
                    "result_history": {},
                    "formal_problem": formal_problem,
                    "formal_solution": "",
                    "iteration_logs": [],
                    "extra_info": extra_info,
                }
                filepath = save_json(result_data, str(results_dir), run_id)

                return {
                    "problem_id": problem_id,
                    "result": VerifyResult.ERROR,
                    "success_steps": 0,
                    "formal_problem": formal_problem,
                    "formal_solution": "",
                    "extra_info": extra_info,
                    "result_path": str(filepath),
                }
            finally:
                cleanup_logger(problem_logger)

    pid_to_formal = {p.get("problem_id", "unknown"): p.get("formal_problem", "") for p in problems}

    total_tasks = len(problems) * pass_k
    max_workers = min(total_tasks, cfg.max_workers)

    problem_runs: Dict[str, list] = defaultdict(list)

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {}
        for p in problems:
            pid = p.get("problem_id", "unknown")
            for attempt in range(pass_k):
                future = executor.submit(process_one_problem, p, attempt)
                futures[future] = (pid, attempt)

        with tqdm(total=total_tasks, desc="[Decompose] Progress", unit="task") as pbar:
            for future in as_completed(futures):
                pid, attempt = futures.pop(future)
                try:
                    meta = future.result()
                    r_result = meta["result"]
                    r_score = meta["extra_info"].get("final_score", float('inf'))
                    r_path = meta["result_path"]

                    problem_runs[pid].append((attempt, r_result.value, r_score, r_path))

                    score_str = f", score={r_score}" if pass_k > 1 else ""
                    attempt_str = f" (attempt {len(problem_runs[pid])}/{pass_k})" if pass_k > 1 else ""

                    if r_result == VerifyResult.PROVE_NO_SORRY:
                        logger.info(f"  [Decompose] {pid}{attempt_str}: fully proved ({meta['success_steps']}  steps){score_str}")
                    elif r_result == VerifyResult.CHECK_SUCCESS:
                        logger.info(f"  [Decompose] {pid}{attempt_str}: Check passed ({meta['success_steps']}  steps){score_str}")
                    else:
                        err_msg = f", error={meta['extra_info'].get('last_error', 'unknown')[:300]}" if r_result == VerifyResult.ERROR else ""
                        logger.warning(f"  [Decompose] {pid}{attempt_str}: {r_result.value}{score_str}{err_msg}")

                except BudgetExceededError as e:
                    logger.error(f"[Decompose] Budget exceeded: {e}")
                    for f in futures:
                        f.cancel()
                    break
                except Exception as e:
                    logger.error(f"  [Decompose] {pid}: {e}")
                    extra_info = {"initial_score": 0, "final_score": float('inf'), "last_error": str(e)}
                    run_id = f"{pid}_a{attempt}" if pass_k > 1 else pid
                    result_data = {
                        "problem_id": pid,
                        "result": VerifyResult.ERROR.value,
                        "success_steps": 0,
                        "result_history": {},
                        "formal_problem": pid_to_formal.get(pid, ""),
                        "formal_solution": "",
                        "iteration_logs": [],
                        "extra_info": extra_info,
                    }
                    filepath = save_json(result_data, str(results_dir), run_id)
                    problem_runs[pid].append((attempt, VerifyResult.ERROR.value, float('inf'), str(filepath)))

                pbar.update(1)

    # Aggregation phase
    logger.info(f"[Decompose] All tasks complete, starting aggregation (loading from disk on demand)...")

    result_stats = Counter()
    all_solutions = []
    iter_log_file = Path(output_dir) / f"iteration_logs_{timestamp}.json"
    iter_log_file.parent.mkdir(parents=True, exist_ok=True)
    first_entry = True
    with open(iter_log_file, "w", encoding="utf-8") as iter_log_f:
        iter_log_f.write("[\n")
        for pid in sorted(problem_runs.keys()):
            runs = problem_runs[pid]

            loaded_runs: Dict[str, dict] = {}
            for attempt_id, result_value, score, path_str in runs:
                run_data = load_json(Path(path_str))
                if run_data is not None:
                    loaded_runs[path_str] = run_data

            candidates = []
            for attempt_id, result_value, score, path_str in runs:
                run_data = loaded_runs.get(path_str)
                if run_data is None:
                    continue
                formal_problem = run_data.get("formal_problem", "")
                for iter_log in run_data.get("iteration_logs", []):
                    iter_result_str = iter_log.get("result")
                    output_code = iter_log.get("output_code")
                    output_scores = iter_log.get("output_scores")
                    if iter_result_str in (VerifyResult.PROVE_NO_SORRY.value, VerifyResult.CHECK_SUCCESS.value) and output_code:
                        r = VerifyResult.PROVE_NO_SORRY if iter_result_str == VerifyResult.PROVE_NO_SORRY.value else VerifyResult.CHECK_SUCCESS
                        s = calculate_reduction_score(output_scores) if output_scores else float('inf')
                        candidates.append((formal_problem, output_code, r, s))

            if not candidates:
                for attempt_id, result_value, score, path_str in runs:
                    run_data = loaded_runs.get(path_str)
                    if run_data is None:
                        continue
                    r = VerifyResult(result_value) if result_value in [v.value for v in VerifyResult] else VerifyResult.ERROR
                    candidates.append((
                        run_data.get("formal_problem", ""),
                        run_data.get("formal_solution", ""),
                        r,
                        run_data.get("extra_info", {}).get("final_score", float('inf')),
                    ))

            if not candidates:
                del loaded_runs
                continue

            best_fp, best_fs, best_result, best_score = _select_best(candidates, cfg.max_lemmas)
            result_stats[best_result] += 1

            all_solutions.append({
                "problem_id": pid,
                "formal_problem": best_fp,
                "formal_solution": best_fs,
                "decompose_result": best_result.value,
            })

            num_lemmas = _count_lemmas(best_fs)
            logger.info(f"  [Decompose] {pid}: Selected best from {len(candidates)} candidates → {best_result.value} (score={best_score:.1f}, lemmas={num_lemmas})")

            attempts_log = []
            for attempt_id, result_value, score, path_str in sorted(runs, key=lambda x: x[0]):
                run_data = loaded_runs.get(path_str)
                if run_data:
                    attempts_log.append({
                        "attempt": attempt_id,
                        "result": result_value,
                        "final_score": run_data.get("extra_info", {}).get("final_score"),
                        "success_steps": run_data.get("success_steps", 0),
                        "iterations": run_data.get("iteration_logs", []),
                    })

            log_entry = {
                "problem_id": pid,
                "formal_problem": best_fp,
                "final_result": best_result.value,
                "final_score": best_score,
                "num_candidates": len(candidates),
                "num_lemmas": num_lemmas,
                "attempts": attempts_log,
            }
            entry_str = json.dumps(log_entry, ensure_ascii=False, indent=2)
            indented = "\n".join("  " + line for line in entry_str.split("\n"))
            if first_entry:
                iter_log_f.write(indented)
                first_entry = False
            else:
                iter_log_f.write(",\n" + indented)
            iter_log_f.write("\n")

            del loaded_runs, candidates, attempts_log

        iter_log_f.write("]\n")
    logger.info(f"[Decompose] Iteration logs saved to: {iter_log_file}")

    all_solutions.sort(key=lambda x: x["problem_id"])
    output_file = Path(output_dir) / f"decomposed_formal_solutions_{timestamp}.json"
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, "w", encoding="utf-8") as f:
        json.dump(all_solutions, f, ensure_ascii=False, indent=2)
    logger.info(f"[Decompose] Decomposition results saved to: {output_file}")

    categories = summarize_categories(result_stats)
    logger.info(f"[Decompose] Category statistics: {categories}")

    usage = get_usage_stats()
    logger.info(f"[Decompose] Token usage: input={usage['prompt_tokens']:,}, output={usage['completion_tokens']:,}, cost=${usage['estimated_cost_usd']:.4f}")

    from decomposer.verifier import close_http_session
    close_http_session()

    main_fh.close()
    logger.removeHandler(main_fh)

    return all_solutions
