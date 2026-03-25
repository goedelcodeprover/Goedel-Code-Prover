#!/usr/bin/env python3
"""
API Prover - Prove Lean lemmas using Azure GPT

Main script: reads JSON data and proves sorry in each lemma.
"""
from __future__ import annotations

import argparse
import asyncio
import json
import logging
import sys
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from prover.config import Config, get_config
from prover.lean_client import (
    verify_lean_code,
    verify_lean_code_async,
    check_verification_result,
    extract_unsolved_goals,
    check_cheating_async,
    close_aiohttp_session,
)
from prover.llm_client import generate_proof
from prover.diff_utils import apply_diff, extract_diffs, validate_changes_within_evolve_block, restore_evolve_block_markers
from prover.sorry_revise import sorry_revise
from common.constants import QUICKCHECK_TACTIC
from common.logger import setup_problem_logger, cleanup_logger, suppress_noisy_loggers
from common.io_utils import save_json, load_json, safe_filename

logger = logging.getLogger(__name__)

def _setup_module_logging():
    """Only configure root logger when running this module directly; when imported as a library, the caller configures it"""
    if not logging.root.handlers:
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s',
            handlers=[logging.StreamHandler(sys.stdout)],
        )
    suppress_noisy_loggers()


def setup_prove_logger(problem_id: str, log_dir: str) -> logging.Logger:
    """Create per-problem log logger (delegated to common.logger)"""
    return setup_problem_logger(problem_id, log_dir, prefix="prove", propagate=False)


class IterationRecord:
    """Single iteration record"""
    def __init__(
        self,
        iteration: int,
        goal_info: dict,
        prompt: dict,  # system_prompt, user_prompt, model
        llm_response: str,
        lean_result: dict,
        diff_applied: bool,
        new_code: str = None,
        error: str = None,
    ):
        self.iteration = iteration
        self.goal_info = goal_info
        self.prompt = prompt
        self.llm_response = llm_response
        self.lean_result = lean_result
        self.diff_applied = diff_applied
        self.new_code = new_code
        self.error = error
    
    def to_dict(self) -> dict:
        return {
            "iteration": self.iteration,
            "goal_info": self.goal_info,
            "prompt": self.prompt,
            "llm_response": self.llm_response,
            "lean_result": self.lean_result,
            "diff_applied": self.diff_applied,
            "new_code": self.new_code,
            "error": self.error,
        }


def _light_iteration_record(r: IterationRecord) -> IterationRecord:
    """Keep only iteration metadata without prompt/llm_response/lean_result/new_code to reduce memory usage"""
    return IterationRecord(
        iteration=r.iteration,
        goal_info=r.goal_info,
        prompt={},
        llm_response="",
        lean_result=None,
        diff_applied=r.diff_applied,
        new_code=None,
        error=r.error,
    )


class ProofResult:
    """Proof result"""
    def __init__(
        self,
        problem_id: str,
        success: bool,
        final_code: str,
        attempts: int,
        remaining_sorries: int,
        error_message: str = "",
        iterations: list = None,
    ):
        self.problem_id = problem_id
        self.success = success
        self.final_code = final_code
        self.attempts = attempts
        self.remaining_sorries = remaining_sorries
        self.error_message = error_message
        self.iterations = iterations or []
    
    def to_dict(self) -> dict:
        return {
            "problem_id": self.problem_id,
            "success": self.success,
            "attempts": self.attempts,
            "remaining_sorries": self.remaining_sorries,
            "error_message": self.error_message,
            "iterations": [it.to_dict() for it in self.iterations],
        }


async def _try_llm_step(
    code: str,
    goal: Dict,
    config: Config,
    error_messages: str,
    strategy: str,
    iteration_num: int,
    llm_semaphore: asyncio.Semaphore = None,
    lean_semaphore: asyncio.Semaphore = None,
    plogger: logging.Logger = None,
) -> tuple[bool, bool, str, str, IterationRecord]:
    """
    Execute one LLM call step
    
    Returns:
        (is_valid_no_sorry, is_valid_with_sorry, new_code, new_errors, record)
    """
    logger = plogger if plogger is not None else logging.getLogger(__name__)
    async def _call_llm():
        return await generate_proof(
            code=code,
            goal_info=goal,
            config=config,
            error_messages=error_messages,
            strategy=strategy,
        )
    
    if llm_semaphore:
        async with llm_semaphore:
            llm_result = await _call_llm()
    else:
        llm_result = await _call_llm()
    
    llm_response = llm_result["response"]
    logger.info(f"LLM Response: {llm_response}")
    
    # LLM returned None or non-string; cannot do regex/string processing, would raise expected string or bytes-like object
    if llm_response is None:
        logger.warning(f"      LLM returned invalid response (None)")
        record = IterationRecord(
            iteration=iteration_num,
            goal_info=goal,
            prompt={"system_prompt": llm_result["system_prompt"], "user_prompt": llm_result["user_prompt"], "model": llm_result["model"], "strategy": strategy},
            llm_response=llm_response,
            lean_result=None,
            diff_applied=False,
            error="LLM returned None or non-string response",
        )
        return False, False, code, error_messages, record

    # Check if there are diffs
    diffs = extract_diffs(llm_response)
    if not diffs:
        logger.warning(f"      No SEARCH/REPLACE format found in LLM response")
        record = IterationRecord(
            iteration=iteration_num,
            goal_info=goal,
            prompt={"system_prompt": llm_result["system_prompt"], "user_prompt": llm_result["user_prompt"], "model": llm_result["model"], "strategy": strategy},
            llm_response=llm_response,
            lean_result=None,
            diff_applied=False,
            error="No SEARCH/REPLACE found",
        )
        return False, False, code, error_messages, record
    
    # Apply diff
    new_code, all_applied, block_results = apply_diff(code, llm_response)
    
    # Post-processing: if the model removed EVOLVE-BLOCK markers, restore them
    new_code = restore_evolve_block_markers(code, new_code)
    
    if not all_applied:
        failed = [r for r in block_results if not r["applied"]]
        logger.warning(f"      Diff apply failed: {len(failed)}/{len(block_results)} blocks unmatched")
        record = IterationRecord(
            iteration=iteration_num,
            goal_info=goal,
            prompt={"system_prompt": llm_result["system_prompt"], "user_prompt": llm_result["user_prompt"], "model": llm_result["model"], "strategy": strategy},
            llm_response=llm_response,
            lean_result=None,
            diff_applied=False,
            error=f"Diff apply failed: {len(failed)}/{len(block_results)} blocks",
        )
        return False, False, code, error_messages, record
    
    # Validate that changes are within the EVOLVE-BLOCK range
    is_valid_block, block_error = validate_changes_within_evolve_block(code, new_code)
    if not is_valid_block:
        logger.warning(f"      Changes outside EVOLVE-BLOCK range: {block_error}")
        record = IterationRecord(
            iteration=iteration_num,
            goal_info=goal,
            prompt={"system_prompt": llm_result["system_prompt"], "user_prompt": llm_result["user_prompt"], "model": llm_result["model"], "strategy": strategy},
            llm_response=llm_response,
            lean_result=None,
            diff_applied=False,
            error=f"Changes outside EVOLVE-BLOCK: {block_error}",
        )
        return False, False, code, error_messages, record
    
    lean_result = await _verify_with_semaphore(new_code, config, lean_semaphore)
    is_valid_no_sorry, is_valid_with_sorry, errors = check_verification_result(lean_result)
    
    record = IterationRecord(
        iteration=iteration_num,
        goal_info=goal,
        prompt={"system_prompt": llm_result["system_prompt"], "user_prompt": llm_result["user_prompt"], "model": llm_result["model"], "strategy": strategy},
        llm_response=llm_response,
        lean_result=lean_result,
        diff_applied=True,
        new_code=new_code,
    )
    
    new_errors = "\n".join(errors) if errors else ""
    
    if not is_valid_with_sorry:
        logger.warning(f"      Compilation failed: {new_errors if errors else 'unknown'}...")
    
    return is_valid_no_sorry, is_valid_with_sorry, new_code, new_errors, record


async def _check_and_create_success_result(
    problem_id: str,
    original_code: str,
    final_code: str,
    iteration_num: int,
    all_iterations: list,
    config: Config,
    results_dir: str,
    spec_code: str,
    lean_semaphore: asyncio.Semaphore = None,
    plogger: logging.Logger = None,
) -> tuple[bool, ProofResult | None]:
    """
    Check if proof is valid (no cheating); if valid, create success result
    
    Args:
        problem_id: Problem ID
        original_code: Original code (formal_solution)
        final_code: Final proof code
        iteration_num: Number of iterations
        all_iterations: All iteration records
        config: Configuration
        results_dir: Results save directory
        spec_code: Code for extracting original theorem signature (formal_problem)
        plogger: Per-problem log logger
        
    Returns:
        (is_valid, proof_result)
        - is_valid: True if proof is valid (no cheating)
        - proof_result: Returns ProofResult if valid; otherwise None
    """
    logger = plogger if plogger is not None else logging.getLogger(__name__)
    if lean_semaphore:
        async with lean_semaphore:
            is_cheating, cheating_error, axioms = await check_cheating_async(final_code, spec_code, config)
    else:
        is_cheating, cheating_error, axioms = await check_cheating_async(final_code, spec_code, config)
    
    if is_cheating:
        logger.warning(f"⚠️ Cheating detected: {cheating_error}")
        return False, None
    
    # No cheating, create success result
    proof_result = ProofResult(
        problem_id=problem_id,
        success=True,
        final_code=final_code,
        attempts=iteration_num,
        remaining_sorries=0,
        iterations=all_iterations,
    )
    _save_result_json(problem_id, original_code, proof_result, results_dir, plogger=logger)
    
    if axioms:
        logger.info(f"  Axioms used: {axioms}")
    
    return True, proof_result


async def _verify_with_semaphore(code: str, config: Config, lean_semaphore: asyncio.Semaphore = None):
    """Unified lean verification entry point with automatic semaphore handling"""
    if lean_semaphore:
        async with lean_semaphore:
            return await verify_lean_code_async(code, config)
    return await verify_lean_code_async(code, config)


def _record_iteration(
    record: "IterationRecord",
    problem_id: str,
    results_dir: str,
    all_iterations: list,
) -> None:
    """Record one iteration (write to disk + append to in-memory list)"""
    if results_dir:
        _append_iteration_to_disk(problem_id, results_dir, record.to_dict())
        all_iterations.append(_light_iteration_record(record))
    else:
        all_iterations.append(record)


def _make_error_record(iteration_num: int, goal: dict, error: str, strategy: str = "") -> "IterationRecord":
    """Create an IterationRecord for error paths"""
    prompt = {"strategy": strategy} if strategy else {}
    return IterationRecord(
        iteration=iteration_num,
        goal_info=goal,
        prompt=prompt,
        llm_response="",
        lean_result=None,
        diff_applied=False,
        error=str(error),
    )


async def prove_lemma(
    problem_id: str,
    formal_solution: str,
    formal_problem: str,
    config: Config,
    results_dir: str = None,
    cancel_event: asyncio.Event = None,
    llm_semaphore: asyncio.Semaphore = None,
    lean_semaphore: asyncio.Semaphore = None,
    plogger: logging.Logger = None,
) -> ProofResult:
    """
    Prove all sorry in a lemma (epoch iteration mode)
    
    Each epoch processes the entire code:
        1. fix (i times): use prove if no compilation errors, use fix if there are
        2. eliminate (1 time): eliminate compilation errors with sorry
        3. sorry hard-replace (1 time): directly replace the entire proof body
    
    Each epoch continues based on the result of the previous epoch.
    
    Args:
        problem_id: Problem ID
        formal_solution: Lean code with sorry
        config: Configuration
        results_dir: Results save directory
        cancel_event: If another run has succeeded, this event will be set and this run terminates early
        plogger: Per-problem log logger (detailed process written to separate log file)
        
    Returns:
        ProofResult
    """
    logger = plogger if plogger is not None else logging.getLogger(__name__)
    original_code = formal_solution
    current_code = formal_solution
    all_iterations = []
    iteration_num = 0

    # This run writes iteration records to JSONL; memory holds only lightweight placeholders; assembled from file on disk
    if results_dir:
        it_path = _iterations_file_path(problem_id, results_dir)
        if it_path:
            it_path.parent.mkdir(parents=True, exist_ok=True)
            it_path.write_text("", encoding="utf-8")
    
    num_epochs = config.prover.num_epochs
    fix_attempts = config.prover.fix_attempts_per_epoch
    max_total_attempts = config.prover.max_total_attempts
    
    logger.info(f"\n{'='*60}")
    logger.info(f"Starting proof: {problem_id}")
    logger.info(f"{'='*60}")
    
    for epoch in range(num_epochs):
        # Check if another run has succeeded (pass@k early stopping)
        if cancel_event and cancel_event.is_set():
            logger.info(f"Another run succeeded, terminating early: {problem_id}")
            break
        
        # Check if total attempt limit is exceeded
        if iteration_num >= max_total_attempts:
            logger.warning(f"Maximum total attempts reached {max_total_attempts}, stopping proof")
            break
        
        logger.info(f"\n=== Epoch {epoch + 1}/{num_epochs} ===")
        
        # Verify current code and get status
        result = await _verify_with_semaphore(current_code, config, lean_semaphore)
        is_valid_no_sorry, is_valid_with_sorry, errors = check_verification_result(result)
        
        # Check if proof is fully complete
        if is_valid_no_sorry:
            logger.info(f"🎉 Proof complete! No sorry and compilation passed, verifying...")
            is_valid, proof_result = await _check_and_create_success_result(
                problem_id, original_code, current_code, iteration_num,
                all_iterations, config, results_dir, spec_code=formal_problem,
                lean_semaphore=lean_semaphore, plogger=logger,
            )
            if is_valid:
                return proof_result
            else:
                logger.warning(f"  Proof rejected (cheating detected), resetting to original code and retrying...")
                current_code = original_code
                # Re-verify original code to get correct goals/errors
                result = await _verify_with_semaphore(current_code, config, lean_semaphore)
                is_valid_no_sorry, is_valid_with_sorry, errors = check_verification_result(result)
        
        # Get goal information
        goals = extract_unsolved_goals(result)
        goal = goals[0] if goals else {}
        current_errors = "\n".join(errors) if errors else ""
        
        logger.info(f"  Current status: is_valid_with_sorry={is_valid_with_sorry}, goals={len(goals)}, errors={len(errors)}")
        
        # =========== Stage 1: Fix (i times) ===========
        for fix_attempt in range(fix_attempts):
            # Check if another run has succeeded
            if cancel_event and cancel_event.is_set():
                logger.info(f"Another run succeeded, terminating early in fix stage: {problem_id}")
                break
            
            # Use prove (prove sorry) if no compilation errors, use fix if there are
            strategy = "prove" if is_valid_with_sorry else "fix"
            
            try:
                logger.info(f"  [{strategy.upper()}] Attempt {fix_attempt + 1}/{fix_attempts}")
                
                no_sorry, with_sorry, new_code, new_errors, record = await _try_llm_step(
                    current_code, goal, config, current_errors, strategy, iteration_num,
                    llm_semaphore=llm_semaphore, lean_semaphore=lean_semaphore,
                    plogger=logger,
                )
                _record_iteration(record, problem_id, results_dir, all_iterations)
                iteration_num += 1
                
                if no_sorry:
                    logger.info(f"  ✓ [{strategy.upper()}] Proof complete! Verifying...")
                    is_valid, proof_result = await _check_and_create_success_result(
                        problem_id, original_code, new_code, iteration_num,
                        all_iterations, config, results_dir, spec_code=formal_problem,
                        lean_semaphore=lean_semaphore, plogger=logger,
                    )
                    if is_valid:
                        return proof_result
                    logger.warning(f"    Proof rejected (cheating detected), continuing...")
                    continue
                
                if not record.diff_applied:
                    continue
                
                current_code = new_code
                current_errors = new_errors
                is_valid_with_sorry = with_sorry
                
                if with_sorry:
                    result = await _verify_with_semaphore(current_code, config, lean_semaphore)
                    goals = extract_unsolved_goals(result)
                    goal = goals[0] if goals else {}
                    logger.info(f"    Compilation passed, remaining {len(goals)} sorry(s)")
                        
            except Exception as e:
                logger.error(f"  ✗ [{strategy.upper()}] Error: {e}")
                _record_iteration(
                    _make_error_record(iteration_num, goal, e, strategy),
                    problem_id, results_dir, all_iterations,
                )
                iteration_num += 1
        
        # =========== Stage 2: Eliminate (1 time) ===========
        if cancel_event and cancel_event.is_set():
            logger.info(f"Another run succeeded, skipping eliminate/sorry replace: {problem_id}")
            continue
        if not is_valid_with_sorry and current_errors:
            try:
                logger.info(f"  [ELIMINATE] Attempting to eliminate errors with sorry")
                
                no_sorry, with_sorry, new_code, new_errors, record = await _try_llm_step(
                    current_code, goal, config, current_errors, "eliminate", iteration_num,
                    llm_semaphore=llm_semaphore, lean_semaphore=lean_semaphore,
                    plogger=logger,
                )
                _record_iteration(record, problem_id, results_dir, all_iterations)
                iteration_num += 1
                
                if no_sorry:
                    logger.info(f"  ✓ [ELIMINATE] Proof complete! Verifying...")
                    is_valid, proof_result = await _check_and_create_success_result(
                        problem_id, original_code, new_code, iteration_num,
                        all_iterations, config, results_dir, spec_code=formal_problem,
                        lean_semaphore=lean_semaphore, plogger=logger,
                    )
                    if is_valid:
                        return proof_result
                    logger.warning(f"    Proof rejected (cheating detected), not updating state")
                elif record.diff_applied:
                    current_code = new_code
                    current_errors = new_errors
                    is_valid_with_sorry = with_sorry
                    if with_sorry:
                        logger.info(f"  ✓ [ELIMINATE] Compilation passed")
                        
            except Exception as e:
                logger.error(f"  ✗ [ELIMINATE] Error: {e}")
                _record_iteration(
                    _make_error_record(iteration_num, goal, e, "eliminate"),
                    problem_id, results_dir, all_iterations,
                )
                iteration_num += 1
        
        # =========== Stage 3: Sorry hard-replace (1 time) ===========
        if cancel_event and cancel_event.is_set():
            continue
        if not is_valid_with_sorry and current_errors:
            try:
                logger.info(f"  [SORRY REPLACE] Attempting hard replace")
                
                error_list = current_errors.split('\n') if current_errors else []
                revised_code, replace_success, revised_names = sorry_revise(current_code, error_list)
                
                if replace_success:
                    lean_result = await _verify_with_semaphore(revised_code, config, lean_semaphore)
                    no_sorry, with_sorry, new_errors_list = check_verification_result(lean_result)
                    
                    record = IterationRecord(
                        iteration=iteration_num,
                        goal_info=goal,
                        prompt={"strategy": "sorry_replace", "revised_theorems": revised_names},
                        llm_response=f"Sorry replaced: {revised_names}",
                        lean_result=lean_result,
                        diff_applied=True,
                        new_code=revised_code,
                    )
                    _record_iteration(record, problem_id, results_dir, all_iterations)
                    iteration_num += 1
                    
                    if no_sorry:
                        logger.info(f"  ✓ [SORRY REPLACE] Proof complete! Verifying...")
                        is_valid, proof_result = await _check_and_create_success_result(
                            problem_id, original_code, revised_code, iteration_num,
                            all_iterations, config, results_dir, spec_code=formal_problem,
                            lean_semaphore=lean_semaphore, plogger=logger,
                        )
                        if is_valid:
                            return proof_result
                        logger.warning(f"    Proof rejected (cheating detected), not updating state")
                    else:
                        current_code = revised_code
                        current_errors = "\n".join(new_errors_list) if new_errors_list else ""
                        is_valid_with_sorry = with_sorry
                        if with_sorry:
                            logger.info(f"  ✓ [SORRY REPLACE] Compilation passed (replaced: {revised_names})")
                else:
                    logger.warning(f"  ✗ [SORRY REPLACE] Cannot locate theorem to replace")
                    _record_iteration(
                        _make_error_record(iteration_num, goal, "Cannot locate theorem to replace", "sorry_replace"),
                        problem_id, results_dir, all_iterations,
                    )
                    iteration_num += 1
                    
            except Exception as e:
                logger.error(f"  ✗ [SORRY REPLACE] Error: {e}")
                _record_iteration(
                    _make_error_record(iteration_num, goal, e, "sorry_replace"),
                    problem_id, results_dir, all_iterations,
                )
                iteration_num += 1
        
        logger.info(f"=== Epoch {epoch + 1} complete ===")
    
    # All epochs finished
    logger.warning(f"All {num_epochs} epochs completed, unable to prove")
    
    final_result = await _verify_with_semaphore(current_code, config, lean_semaphore)
    final_goals = extract_unsolved_goals(final_result)
    
    proof_result = ProofResult(
        problem_id=problem_id,
        success=False,
        final_code=current_code,
        attempts=iteration_num,
        remaining_sorries=len(final_goals),
        error_message="Max epochs reached or unable to prove",
        iterations=all_iterations,
    )
    _save_result_json(problem_id, original_code, proof_result, results_dir, plogger=logger)
    return proof_result


def _save_result_json(problem_id: str, original_code: str, result: ProofResult, results_dir: str, plogger: logging.Logger = None):
    """Save single problem result to JSON file. iterations are assembled from JSONL first to avoid holding complete records in memory."""
    _logger = plogger if plogger is not None else logging.getLogger(__name__)
    if not results_dir:
        return

    iterations_data = _load_iterations_from_disk(problem_id, results_dir)
    if iterations_data is None:
        iterations_data = [it.to_dict() for it in result.iterations]

    data = {
        "problem_id": problem_id,
        "original_code": original_code,
        "final_code": result.final_code,
        "success": result.success,
        "attempts": result.attempts,
        "remaining_sorries": result.remaining_sorries,
        "error_message": result.error_message,
        "iterations": iterations_data,
    }

    filepath = save_json(data, results_dir, problem_id)
    _logger.info(f"Results saved: {filepath}")


def _result_path(problem_id: str, results_dir: str) -> Path | None:
    """Return the result file path for a run (consistent with _save_result_json naming)"""
    if not results_dir:
        return None
    return Path(results_dir) / safe_filename(problem_id)


def _iterations_file_path(problem_id: str, results_dir: str) -> Path | None:
    """JSONL path for iteration records of a run (one complete iteration dict per line, not held in memory long-term)"""
    if not results_dir:
        return None
    return Path(results_dir) / safe_filename(problem_id, extension=".iterations.jsonl")


def _append_iteration_to_disk(problem_id: str, results_dir: str, record_dict: dict) -> None:
    """Append single iteration record to disk JSONL without using memory"""
    path = _iterations_file_path(problem_id, results_dir)
    if path is None:
        return
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "a", encoding="utf-8") as f:
            f.write(json.dumps(record_dict, ensure_ascii=False) + "\n")
    except Exception as e:
        logger.warning(f"Failed to write iteration record {path}: {e}")


def _load_iterations_from_disk(problem_id: str, results_dir: str) -> list[dict] | None:
    """Assemble iterations list from JSONL for final JSON output"""
    path = _iterations_file_path(problem_id, results_dir)
    if path is None or not path.exists():
        return None
    out = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                out.append(json.loads(line))
        return out if out else None
    except Exception as e:
        logger.warning(f"Failed to read iteration records {path}: {e}")
        return None


def _load_result_json(path: Path) -> dict | None:
    """Load single run result from disk (for on-demand output construction, avoiding full memory retention)."""
    return load_json(path)


async def prove_all(
    data_path: str,
    config: Config,
    output_path: str = None,
    results_dir: str = None,
    limit: int = None,
    log_dir: str = None,
    summary_logger: logging.Logger = None,
) -> list[ProofResult]:
    """
    Prove all lemmas in the JSON file (concurrent processing)
    
    Args:
        data_path: JSON data file path
        config: Configuration
        output_path: Output file path
        results_dir: Results directory for each problem
        limit: Maximum number of problems to process
        log_dir: Log directory (for per-problem log files)
        summary_logger: Summary logger (writes to main log file)
        
    Returns:
        AllProof result
    """
    slogger = summary_logger or logger  # Summary log: main log file + console
    # Ensure results directory exists
    if results_dir:
        Path(results_dir).mkdir(parents=True, exist_ok=True)
    
    # Read data
    with open(data_path, 'r') as f:
        data = json.load(f)
    
    if limit:
        data = data[:limit]
    
    logger.info(f"Loaded {len(data)} problems")
    
    # Results disproved/unproven in decompose stage; prove stage skips them without calling LLM
    DISPROVED_DECOMPOSE_RESULTS = ("quickcheck_failed", "prove_theorem_failed")
    disproved_ids = set()
    # Pre-check with QuickCheck before concurrency: only treat as disprove success when error_message contains counterexample text (e.g. "Found a counter-example!")
    quickcheck_disproved_ids = set()

    def _error_looks_like_counterexample(error_list: list) -> bool:
        """Only treat as counterexample disproof when error message contains counterexample text (e.g. Found a counter-example!)"""
        if not error_list:
            return False
        combined = " ".join(str(e).lower() for e in error_list)
        return (
            "counter-example" in combined
            or "counterexample" in combined
            or "found a counter" in combined
        )

    # First pass: collect problems needing QuickCheck, no-sorry problems, and decompose-disproved problems
    qc_candidates = []  # (problem_id, formal_solution, formal_problem, qc_code)
    no_sorry_tasks = []
    for i, item in enumerate(data):
        problem_id = item.get("problem_id", f"problem_{i}")
        formal_solution = item.get("formal_solution", "")
        formal_problem = item.get("formal_problem", "")
        if item.get("decompose_result") in DISPROVED_DECOMPOSE_RESULTS:
            disproved_ids.add(problem_id)
            if slogger:
                slogger.info(f"  [Prove] {problem_id}: Decompose found counterexample/unproven ({item.get('decompose_result')}), skipping proof")
            continue
        if not formal_solution:
            if formal_problem:
                formal_solution = formal_problem
            else:
                continue
        if not formal_problem:
            continue
        code_for_qc = formal_solution if formal_solution else formal_problem
        if "sorry" in code_for_qc:
            qc_code = code_for_qc.replace("sorry", QUICKCHECK_TACTIC)
            qc_candidates.append((problem_id, formal_solution, formal_problem, qc_code))
        else:
            logger.info(f"{problem_id}: No sorry, will verify directly")
            no_sorry_tasks.append((problem_id, formal_solution, formal_problem))

    # Concurrent QuickCheck pre-check
    if qc_candidates:
        qc_workers = min(len(qc_candidates), config.prover.lean_max_concurrent or 64)
        logger.info(f"QuickCheck pre-check concurrent execution: {len(qc_candidates)} problems, concurrency={qc_workers}")
        def _run_one_qc(item):
            pid, _, _, qc_code = item
            return (pid, verify_lean_code(qc_code, config=config))
        with ThreadPoolExecutor(max_workers=qc_workers) as ex:
            qc_results = list(ex.map(_run_one_qc, qc_candidates))
        for problem_id, qc_result in qc_results:
            is_valid_no_sorry, _, error_list = check_verification_result(qc_result)
            if not is_valid_no_sorry and _error_looks_like_counterexample(error_list):
                quickcheck_disproved_ids.add(problem_id)
                if slogger:
                    slogger.info(f"  [Prove] {problem_id}: QuickCheck found counterexample (Found a counter-example!), treated as disprove success")

    tasks_info = [
        (pid, fs, fp) for (pid, fs, fp, _) in qc_candidates
        if pid not in quickcheck_disproved_ids
    ]
    
    if disproved_ids:
        logger.info(f"Marked as disproved (skipping proof): {len(disproved_ids)}")
    if quickcheck_disproved_ids:
        logger.info(f"QuickCheck pre-check found counterexample (disprove success): {len(quickcheck_disproved_ids)} ")
    logger.info(f"Problems requiring proof: {len(tasks_info)}")
    
    # pass_k: run pass_k times independently per problem
    pass_k = config.prover.pass_k
    
    # Expand to (original_problem_id, run_problem_id, formal_solution, formal_problem, run_idx) list
    all_tasks_info = []
    for problem_id, formal_solution, formal_problem in tasks_info:
        for run_idx in range(pass_k):
            if pass_k > 1:
                run_problem_id = f"{problem_id}_run_{run_idx}"
            else:
                run_problem_id = problem_id
            all_tasks_info.append((problem_id, run_problem_id, formal_solution, formal_problem, run_idx))
    
    if pass_k > 1:
        logger.info(f"pass@{pass_k} mode: {pass_k} times per problem, total {len(all_tasks_info)} tasks")
    
    # Concurrency control (LLM and Lean rate-limited separately)
    llm_semaphore = asyncio.Semaphore(config.prover.max_workers)
    lean_semaphore = asyncio.Semaphore(config.prover.lean_max_concurrent)
    # Task-level concurrency limit: only max_concurrent_tasks tasks run simultaneously to avoid too many open log files causing "Too many open files"
    task_semaphore = asyncio.Semaphore(config.prover.max_concurrent_tasks)
    
    # pass@k early stopping: one Event per problem; when a run succeeds, notify other runs to stop
    problem_success_events: dict[str, asyncio.Event] = {
        pid: asyncio.Event() for pid, _, _ in tasks_info
    }
    
    # Progress tracking
    completed_count = 0
    success_count = 0
    total_tasks = len(all_tasks_info)
    progress_lock = asyncio.Lock()

    async def prove_with_semaphore(
        orig_problem_id: str, run_problem_id: str,
        formal_solution: str, formal_problem: str, run_idx: int,
    ) -> tuple[str, int, ProofResult]:
        """Proof task with concurrency limit, returns (original_problem_id, run_idx, result). Acquires task_semaphore before opening log files to control total FD count."""
        nonlocal completed_count, success_count
        
        async with task_semaphore:
            cancel_event = problem_success_events.get(orig_problem_id)
            
            # Create per-problem logger (only when enabled and log_dir is specified, to avoid excessive FD causing Too many open files)
            plogger = None
            if log_dir and getattr(config.prover, 'enable_per_run_log', True):
                plogger = setup_prove_logger(run_problem_id, log_dir)
            
            try:
                result = await prove_lemma(
                    run_problem_id, formal_solution, formal_problem, config, results_dir,
                    cancel_event=cancel_event,
                    llm_semaphore=llm_semaphore,
                    lean_semaphore=lean_semaphore,
                    plogger=plogger,
                )
                
                # Write per-problem result summary to summary log (main log)
                run_info = f" (run {run_idx})" if pass_k > 1 else ""
                if result.success:
                    slogger.info(f"  [Prove] {run_problem_id}{run_info}: Success ({result.attempts} attempts)")
                else:
                    sorries = result.remaining_sorries
                    err = result.error_message or ""
                    err_str = f", Error={err[:200]}" if err else ""
                    slogger.warning(f"  [Prove] {run_problem_id}{run_info}: Failed ({result.attempts} attempts, remaining {sorries} sorry(s){err_str})")
                
                # Update progress
                async with progress_lock:
                    completed_count += 1
                    if result.success:
                        success_count += 1
                        # Notify other runs of the same problem to stop
                        if cancel_event:
                            cancel_event.set()
                    run_info = f" (run {run_idx})" if pass_k > 1 else ""
                    logger.info(f"\n📊 Progress: {completed_count}/{total_tasks} - Success: {success_count}/{completed_count}{run_info}")
                
                return (orig_problem_id, run_idx, result)
            finally:
                if plogger is not None:
                    cleanup_logger(plogger)
    
    # -----------------------------------------------------------------------
    # Fix: use asyncio.wait(FIRST_COMPLETED) instead of as_completed + dict.pop
    #
    # Original code issues:
    #   1. asyncio.as_completed returns coroutines that cannot be used as dict keys for pop
    #   2. asyncio.gather holds all return values until all complete, accumulating ProofResult in memory
    #
    # Fix:
    #   - asyncio.create_task creates Tasks (Task is hashable, can be used as dict key)
    #   - asyncio.wait(FIRST_COMPLETED) streaming collection: process one as each completes
    #   - Remove from mapping immediately after processing; ProofResult is GC-collected when out of scope
    # -----------------------------------------------------------------------
    logger.info(
        f"Starting concurrent proving (task concurrency={config.prover.max_concurrent_tasks}, "
        f"LLM concurrency={config.prover.max_workers}, Lean concurrency={config.prover.lean_max_concurrent})"
    )

    # Build Task -> (orig_pid, run_idx, run_pid, formal_solution) mapping
    task_to_info: dict[asyncio.Task, tuple] = {}
    for orig_pid, run_pid, fs, fp, ridx in all_tasks_info:
        t = asyncio.create_task(prove_with_semaphore(orig_pid, run_pid, fs, fp, ridx))
        task_to_info[t] = (orig_pid, ridx, run_pid, fs)

    # problem_runs: pid -> [(run_idx, success, path_str)]
    problem_runs: dict[str, list[tuple[int, bool, str]]] = defaultdict(list)

    # Streaming consumption: persist and release memory as each completes, without waiting for all
    pending: set = set(task_to_info.keys())
    while pending:
        done, pending = await asyncio.wait(pending, return_when=asyncio.FIRST_COMPLETED)
        for task in done:
            orig_pid, run_idx, run_pid, formal_solution = task_to_info.pop(task)
            try:
                # Task.result() is a synchronous call, gets the value directly without blocking
                _, _, result = task.result()
            except Exception as e:
                logger.error(f"Task exception {orig_pid} run {run_idx}: {e}")
                result = ProofResult(
                    problem_id=orig_pid,
                    success=False,
                    final_code=formal_solution,
                    attempts=0,
                    remaining_sorries=-1,
                    error_message=str(e),
                )
                if results_dir:
                    _save_result_json(run_pid, formal_solution, result, results_dir)
            
            path = _result_path(run_pid, results_dir)
            path_str = str(path) if path else ""
            problem_runs[orig_pid].append((run_idx, result.success, path_str))
            # result goes out of scope here, collected by GC, no longer accumulating in memory

    # Sort by run_idx for ordered output
    for pid in problem_runs:
        problem_runs[pid].sort(key=lambda x: x[0])

    # Process no-sorry problems (direct verification, no LLM needed)
    if no_sorry_tasks:
        logger.info(f"\nVerifying {len(no_sorry_tasks)} no-sorry problems...")
        
        async def verify_no_sorry(pid, fs, fp):
            """Verify no-sorry problems: compilation check + anti-cheating check"""
            async with lean_semaphore:
                result = await verify_lean_code_async(fs, config)
            is_valid_no_sorry, _, errors = check_verification_result(result)
            
            if is_valid_no_sorry:
                async with lean_semaphore:
                    is_cheating, cheating_error, axioms = await check_cheating_async(fs, fp, config)
                if not is_cheating:
                    proof_result = ProofResult(
                        problem_id=pid, success=True, final_code=fs,
                        attempts=0, remaining_sorries=0,
                    )
                    _save_result_json(pid, fs, proof_result, results_dir)
                    logger.info(f"  ✓ {pid}: No sorry, verification passed")
                    return (pid, proof_result)
                else:
                    logger.warning(f"  ⚠️ {pid}: No sorry but cheating detected: {cheating_error}")
                    error_msg = f"No sorry but cheating detected: {cheating_error}"
            else:
                error_msg = "\n".join(errors) if errors else "Verification failed"
                logger.warning(f"  ✗ {pid}: No sorry but verification failed")
            
            proof_result = ProofResult(
                problem_id=pid, success=False, final_code=fs,
                attempts=0, remaining_sorries=0,
                error_message=error_msg,
            )
            _save_result_json(pid, fs, proof_result, results_dir)
            return (pid, proof_result)
        
        no_sorry_results = await asyncio.gather(*[
            verify_no_sorry(pid, fs, fp) for pid, fs, fp in no_sorry_tasks
        ], return_exceptions=True)
        
        for i, raw in enumerate(no_sorry_results):
            pid = no_sorry_tasks[i][0]
            if isinstance(raw, Exception):
                logger.error(f"Verification exception {pid}: {raw}")
                proof_result = ProofResult(
                    problem_id=pid, success=False, final_code=no_sorry_tasks[i][1],
                    attempts=0, remaining_sorries=0, error_message=str(raw),
                )
                if results_dir:
                    _save_result_json(pid, no_sorry_tasks[i][1], proof_result, results_dir)
                path = _result_path(pid, results_dir)
                problem_runs[pid].append((0, False, str(path) if path else ""))
            else:
                _, proof_result = raw
                path = _result_path(pid, results_dir)
                problem_runs[pid].append((0, proof_result.success, str(path) if path else ""))
                # proof_result no longer retained to avoid memory retention
    
    # Merge all problems (with sorry + without sorry) for statistics
    all_problem_tasks = tasks_info + no_sorry_tasks
    
    # Calculate pass@k success rate (any single success counts as pass)
    num_problems = len(all_problem_tasks)
    pass_k_success = sum(
        1 for pid, _, _ in all_problem_tasks
        if any(success for _, success, _ in problem_runs.get(pid, []))
    )
    
    # Summarize the "best" result per problem (for return value compatibility): load from disk on demand, avoid retaining full ProofResult in memory
    results: list[ProofResult] = []
    for problem_id, formal_solution, formal_problem in all_problem_tasks:
        runs = problem_runs.get(problem_id, [])
        if not runs:
            continue
        # Pick the first successful run; if all failed, use the path of the last run
        best_entry = next(((idx, ok, p) for idx, ok, p in runs if ok), runs[-1])
        _, _, best_path = best_entry
        d = _load_result_json(Path(best_path)) if best_path else None
        if d:
            results.append(ProofResult(
                problem_id=problem_id,
                success=d["success"],
                final_code=d.get("final_code", formal_solution),
                attempts=d.get("attempts", 0),
                remaining_sorries=d.get("remaining_sorries", -1),
                error_message=d.get("error_message", ""),
                iterations=[],  # No longer loading iterations to save memory
            ))
    
    # Summary
    logger.info(f"\n{'='*60}")
    logger.info(f"Proving complete!")
    no_sorry_info = f" (of which {len(no_sorry_tasks)} no-sorry)" if no_sorry_tasks else ""
    logger.info(f"Total: {num_problems} problems{no_sorry_info}" + (f", {len(tasks_info)} requiring proof × {pass_k} times = {total_tasks} tasks" if pass_k > 1 else ""))
    if pass_k > 1:
        logger.info(f"pass@{pass_k} Success: {pass_k_success}/{num_problems} ({100*pass_k_success/num_problems:.1f}%)" if num_problems else "Success: 0")
        # Also calculate pass@1 (only look at run_0)
        pass_1_success = sum(
            1 for pid, _, _ in all_problem_tasks
            if any(success for idx, success, _ in problem_runs.get(pid, []) if idx == 0)
        )
        logger.info(f"pass@1 Success: {pass_1_success}/{num_problems} ({100*pass_1_success/num_problems:.1f}%)" if num_problems else "pass@1: 0")
    else:
        final_success_count = sum(1 for r in results if r.success)
        logger.info(f"Success: {final_success_count} ({100*final_success_count/len(results):.1f}%)" if results else "Success: 0")
    logger.info(f"{'='*60}")
    
    # Save results (load best run per problem on demand from disk, no full ProofResult retention)
    if output_path:
        output_data = []
        for i, item in enumerate(data):
            problem_id = item.get("problem_id", f"problem_{i}")
            runs = problem_runs.get(problem_id, [])
            if not runs:
                if problem_id in quickcheck_disproved_ids:
                    output_data.append({
                        **item,
                        "disproved": True,
                        "proof_result": {
                            "success": True,
                            "attempts": 0,
                            "remaining_sorries": 0,
                            "error_message": "QuickCheck pre-check failed, treated as counterexample disproof (disprove success)",
                        },
                    })
                elif problem_id in disproved_ids:
                    decompose_result = item.get("decompose_result", "")
                    msg = "Decompose stage found counterexample (QuickCheck), skipping proof" if decompose_result == "quickcheck_failed" else "Decompose stage: original theorem unproven, skipping proof"
                    output_data.append({
                        **item,
                        "disproved": True,
                        "proof_result": {
                            "success": False,
                            "attempts": 0,
                            "remaining_sorries": -1,
                            "error_message": msg,
                        },
                    })
                else:
                    output_data.append(item)
                continue
            any_success = any(s for _, s, _ in runs)
            best_entry = next(((idx, s, p) for idx, s, p in runs if s), runs[-1])
            _, _, best_path = best_entry
            d_best = _load_result_json(Path(best_path)) if best_path else None
            proved_solution = (d_best.get("final_code") if d_best and any_success else None)
            if pass_k > 1:
                proof_runs = []
                for run_idx, _, path in runs:
                    d = _load_result_json(Path(path)) if path else None
                    if d:
                        iters = d.get("iterations", [])
                        proof_runs.append({
                            "run_idx": run_idx,
                            "success": d["success"],
                            "attempts": d["attempts"],
                            "remaining_sorries": d["remaining_sorries"],
                            "error_message": d.get("error_message", ""),
                            "iterations_count": len(iters),
                        })
                        # Do not retain iterations content to reduce memory and final JSON size
                output_item = {
                    **item,
                    "proved_solution": proved_solution,
                    "pass_k": pass_k,
                    "pass_k_success": any_success,
                    "proof_runs": proof_runs,
                }
            else:
                if d_best:
                    proof_result = {
                        "success": d_best.get("success"),
                        "attempts": d_best.get("attempts"),
                        "remaining_sorries": d_best.get("remaining_sorries"),
                        "error_message": d_best.get("error_message", ""),
                        "iterations_count": len(d_best.get("iterations", [])),
                    }
                else:
                    proof_result = {}
                output_item = {
                    **item,
                    "proved_solution": proved_solution,
                    "proof_result": proof_result,
                }
            output_data.append(output_item)
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output_data, f, indent=2, ensure_ascii=False)
        logger.info(f"Results saved to: {output_path}")
    
    # Clean up global aiohttp session, release FD and connection pool
    await close_aiohttp_session()
    
    return results


def main():
    _setup_module_logging()
    parser = argparse.ArgumentParser(
        description="Prove Lean lemmas using Azure GPT"
    )
    parser.add_argument(
        "data_path",
        help="Path to JSON data file",
    )
    parser.add_argument(
        "-c", "--config",
        default="config.yaml",
        help="Config file path (default: config.yaml)",
    )
    parser.add_argument(
        "-o", "--output",
        help="Output file path",
    )
    parser.add_argument(
        "-r", "--results-dir",
        default="results",
        help="Results directory for each problem (default: results)",
    )
    parser.add_argument(
        "-n", "--limit",
        type=int,
        help="Maximum number of problems to process",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Show verbose logs",
    )
    
    args = parser.parse_args()
    
    # Load configuration
    config = get_config(args.config)
    
    if args.verbose:
        config.debug = True
        logging.getLogger().setLevel(logging.DEBUG)
    
    # Run
    asyncio.run(prove_all(
        data_path=args.data_path,
        config=config,
        output_path=args.output,
        results_dir=args.results_dir,
        limit=args.limit,
    ))
    
    # Print token usage and cost statistics
    from prover.llm_client import print_usage_stats, get_usage_stats
    print_usage_stats(config)
    stats = get_usage_stats(config)
    logger.info(f"Total cost: ${stats['estimated_cost_usd']:.4f} / ${stats['budget_limit']:.2f}")


if __name__ == "__main__":
    main()