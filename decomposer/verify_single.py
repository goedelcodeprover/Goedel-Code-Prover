"""
Single problem verification module - core logic ported from legacy version
Each problem is processed independently with a complete iteration workflow
"""
from __future__ import annotations

import logging
from collections import Counter

from LeanCodeParser import LeanCodeTree
from LeanCodeParser.utils import replace_sorry_by_tactic
from decomposer.config import DecomposeConfig
from .utils import (
    VerifyResult,
    llm_response,
    get_config,
)
from .verifier import verify_lean_code, verify_lean_code_batch
from .scorer import select_best_target, extract_scores_from_result, calculate_reduction_score, SCORE_CODE_HEADER

def guess_proof(tree: LeanCodeTree, target_name: str, cfg: DecomposeConfig) -> tuple[str, str, str, str]:
    """Generate proof
    
    Returns:
        (code, prompt, raw_content, thinking) - extracted code, input prompt, raw response content, thinking content
    """
    problem = tree.to_code(target_key=target_name)
    if "theorem" not in problem:
        # Replace only the last lemma with theorem
        problem = "theorem".join(problem.rsplit("lemma", 1))
    prompt = cfg.prompt_template.format(theorem_name=target_name, formal_problem=problem)
    code, raw_content, thinking = llm_response(prompt)
    return code, prompt, raw_content, thinking

def revise_proof(tree: LeanCodeTree, result: dict) -> None:
    """Revise the tree based on error messages from verification result.
    
    Args:
        tree: LeanCodeTree to revise (modified in place)
        result: Dictionary containing verification results with error messages
    """
    error_message = result.get("error_message", [False, []])
    feedback = error_message[1]
    tree.revise(feedback)


def _is_tolerable_error(errors: list[str]) -> bool:
    """Check if all errors are tolerable (index out of bounds / PANIC)
    
    These errors are typically edge cases triggered by random data generated
    by quickcheck, not genuine counterexamples, and can be tolerated.
    """
    if not errors:
        return False
    return all(
        "Error: index out of bounds" in e or "PANIC" in e 
        for e in errors
    )


def _compute_score_only(
    code: str, 
    cfg: DecomposeConfig, 
    logger: logging.Logger,
    max_retries: int = 2
) -> int | None:
    """Execute countNodesAll separately to obtain the score
    
    When quickcheck encounters tolerable errors (index out of bounds / PANIC),
    the countNodesAll result may be unreliable and needs to be re-executed separately.
    
    Retries up to max_retries times if score retrieval fails (node_scores is empty).
    
    Returns:
        Score on success, None on failure
    """
    postprocess_code = code.replace("import Tacs", SCORE_CODE_HEADER).replace("sorry", "countNodesAll")
    
    for attempt in range(max_retries + 1):
        result = verify_lean_code(postprocess_code, server_url=cfg.lean_server_url, timeout=cfg.timeout)
        
        node_scores = extract_scores_from_result(result)
        if node_scores:
            score = max(node_scores)
            logger.debug(f"Score computed separately: {score} (attempt {attempt + 1}/{max_retries + 1})")
            return score
        
        if attempt < max_retries:
            logger.debug(f"Failed to retrieve score, retrying ({attempt + 1}/{max_retries})...")
    
    logger.warning(f"Failed to retrieve score after {max_retries} retries")
    return None


def run_quickcheck_with_score(
    code: str,
    cfg: DecomposeConfig,
    logger: logging.Logger
) -> tuple[bool, list[int], str]:
    """Execute quickcheck and compute scores
    
    Logic:
    1. If errors occur and they are not index out of bounds/PANIC -> quickcheck failed
    2. If errors occur and all are index out of bounds/PANIC -> quickcheck passed, recompute scores
    3. If no errors -> quickcheck passed, extract scores directly
    
    Args:
        code: Original Lean code (with sorry)
        cfg: Configuration
        logger: Logger
        
    Returns:
        (quickcheck_passed, scores, error_detail)
        - quickcheck_passed: Whether quickcheck passed
        - scores: List of target complexity scores ordered by sorry occurrence in code (empty list on failure)
        - error_detail: Error details (for logging, empty on success)
    """
    # Use (countNodesAll; quickcheck) combination, compute score first then check counterexamples
    quickcheck_count_nodes = f"(countNodesAll; {cfg.quickcheck_tactic})"
    postprocess_code = code.replace("import Tacs", SCORE_CODE_HEADER).replace("sorry", quickcheck_count_nodes)
    
    result = verify_lean_code(postprocess_code, server_url=cfg.lean_server_url, timeout=cfg.timeout)
    
    # Check timeout
    if result.get("timeout", False):
        return (False, [], "timeout")
    
    error_message = result.get("error_message", [False, []])
    has_error = error_message[0]
    errors = error_message[1] if error_message[1] else []
    
    if has_error and errors:
        if _is_tolerable_error(errors):
            # Only tolerable errors (index out of bounds / PANIC)
            # quickcheck passed, but scores need to be recomputed
            logger.debug("Tolerable errors detected, re-executing countNodesAll to get scores")
            score = _compute_score_only(code, cfg, logger)
            if score is not None:
                return (True, [score], "")
            else:
                # All retries failed, return original quickcheck error
                error_detail = "; ".join(errors[:2])
                return (False, [], f"Failed to compute score: {error_detail}")
        else:
            # Other errors, quickcheck failed
            error_detail = "; ".join(errors[:2])
            return (False, [], error_detail)
    
    # No errors or is_valid_with_sorry, extract score list directly
    if result.get("is_valid_with_sorry", False) or not has_error:
        node_scores = extract_scores_from_result(result)
        return (True, node_scores, "")
    
    # Unknown situation
    return (False, [], f"Unknown error: {result}")


def run_quickcheck_batch_with_scores(
    codes: list[str],
    cfg: DecomposeConfig,
    logger: logging.Logger
) -> list[tuple[bool, int, str]]:
    """Batch execute quickcheck and compute scores
    
    Args:
        codes: List of original Lean code (with sorry)
        cfg: Configuration
        logger: Logger
        
    Returns:
        List where each element is (quickcheck_passed, score, error_detail)
        - score: -1 on failure
    """
    # Use (countNodesAll; quickcheck) combination
    quickcheck_count_nodes = f"(countNodesAll; {cfg.quickcheck_tactic})"
    postprocess_codes = [
        code.replace("import Tacs", SCORE_CODE_HEADER).replace("sorry", quickcheck_count_nodes)
        for code in codes
    ]
    
    # Batch verify
    results = verify_lean_code_batch(postprocess_codes, server_url=cfg.lean_server_url, timeout=cfg.timeout)
    
    # Process each result
    output = []
    for i, result in enumerate(results):
        if result is None:
            output.append((False, -1, "no response"))
            continue
            
        # Check timeout
        if result.get("timeout", False):
            output.append((False, -1, "timeout"))
            continue
        
        error_message = result.get("error_message", [False, []])
        has_error = error_message[0]
        errors = error_message[1] if error_message[1] else []
        
        if has_error and errors:
            if _is_tolerable_error(errors):
                # Only tolerable errors, recompute scores
                logger.debug(f"Code {i}: tolerable errors detected, re-executing countNodesAll")
                score = _compute_score_only(codes[i], cfg, logger)
                if score is not None:
                    output.append((True, score, ""))
                else:
                    # All retries failed, return original quickcheck error
                    error_detail = "; ".join(errors[:2])
                    output.append((False, -1, f"Failed to compute score: {error_detail}"))
            else:
                # Other errors
                error_detail = "; ".join(errors[:2])
                output.append((False, -1, error_detail))
        elif result.get("is_valid_with_sorry", False) or not has_error:
            # Extract scores directly
            node_scores = extract_scores_from_result(result)
            score = max(node_scores) if node_scores else 0
            output.append((True, score, ""))
        else:
            output.append((False, -1, f"unknown error"))
    
    return output


def initialize_scores(
    tree: LeanCodeTree, 
    logger: logging.Logger, 
    cfg: DecomposeConfig
) -> tuple[dict[str, int], list[str]]:
    """Initialize score cache: run quickcheck and compute scores for all initial targets
    
    Args:
        tree: Lean code tree
        logger: Logger
        cfg: Configuration
        
    Returns:
        (score cache {target_key: score}, list of error messages)
        Score is -1 if quickcheck fails during initialization
    """
    score_cache: dict[str, int] = {}
    init_errors: list[str] = []
    
    # Collect all leaf nodes containing sorry
    candidates = [(node.key, node) for node in tree.walk_leaves() if node.payload.has_sorry]
    
    if not candidates:
        logger.info("Initialization: no targets to prove")
        return score_cache, init_errors
    else:
        assert len(candidates) == 1, f"Found multiple targets during initialization: {candidates}, but only one is allowed"
    
    # Generate code
    code = tree.to_code()
    logger.debug(f"Initialization code: {code}")
    
    # Execute quickcheck and compute scores
    passed, scores, error_detail = run_quickcheck_with_score(code, cfg, logger)
    
    # Extract scores and populate cache (only one candidate)
    target_key, _ = candidates[0]
    if passed:
        # Only one sorry during initialization, take the first score or max
        score = scores[0] if scores else 0
        score_cache[target_key] = score
        logger.debug(f"Initialization score: {target_key} = {score}")
    else:
        score_cache[target_key] = -1
        init_errors.append(f"{target_key}: {error_detail}")
        logger.warning(f"Initialization score: {target_key} = -1 ({error_detail})")
    
    logger.info(f"Initialization complete, score cache: {score_cache}")
    return score_cache, init_errors


def check_with_quickcheck(
    tree: LeanCodeTree, 
    logger: logging.Logger, 
    cfg: DecomposeConfig,
    score_cache: dict[str, int]
) -> VerifyResult:
    """Check using quickcheck while computing sub-target scores and updating the cache
    
    Optimization strategy:
    - Sorrys with existing scores: keep unchanged (do not execute countNodesAll)
    - New sorrys: replace with (countNodesAll; quickcheck)
    - If tolerable errors occur: new sorrys are only replaced with countNodesAll
    
    Args:
        tree: Lean code tree
        logger: Logger
        cfg: Configuration
        score_cache: Score cache, updated in place
        
    Returns:
        Verification result
    """
    try:
        # Truncate leaf nodes (remove proof bodies, fill with sorry)
        tree.truncate_leaves()
        
        # Collect leaf nodes, distinguishing new from those with existing scores
        sorry_leaves = [(node.key, node) for node in tree.walk_leaves() if node.payload.has_sorry]
        new_sorry_keys = [key for key, _ in sorry_leaves if key not in score_cache]
        cached_sorry_keys = [key for key, _ in sorry_leaves if key in score_cache]
        
        logger.debug(f"New sorry: {new_sorry_keys}, cached sorry: {cached_sorry_keys}")
        
        # Replace new sorrys with (countNodesAll; quickcheck)
        quickcheck_count_nodes = f"(countNodesAll; {cfg.quickcheck_tactic})"
        for key, node in sorry_leaves:
            if key not in score_cache:
                node.payload.content = replace_sorry_by_tactic(node.payload.content, quickcheck_count_nodes)
        
        # Generate code and verify
        code = tree.to_code().replace("import Tacs", SCORE_CODE_HEADER)
        result = verify_lean_code(code, server_url=cfg.lean_server_url, timeout=cfg.timeout)
        
        # Check timeout
        if result.get("timeout", False):
            logger.warning("quickcheck timeout")
            return VerifyResult.CHECK_FAILED
        
        error_message = result.get("error_message", [False, []])
        has_error = error_message[0]
        errors = error_message[1] if error_message[1] else []
        
        # Evaluate result
        if has_error and errors:
            if _is_tolerable_error(errors):
                # Only tolerable errors (index out of bounds / PANIC)
                # quickcheck passed, but scores need to be recomputed (using countNodesAll only)
                logger.debug("Tolerable errors detected, re-executing countNodesAll to get scores")
                
                # Replace new sorrys with countNodesAll only
                tree.truncate_leaves()
                # Re-collect leaf nodes (state may have changed after truncate_leaves)
                for node in tree.walk_leaves():
                    if node.payload.has_sorry and node.key not in score_cache:
                        node.payload.content = replace_sorry_by_tactic(node.payload.content, "countNodesAll")
                
                # Regenerate code and verify
                code = tree.to_code().replace("import Tacs", SCORE_CODE_HEADER)
                result = verify_lean_code(code, server_url=cfg.lean_server_url, timeout=cfg.timeout)
                
                # Extract scores and update cache
                scores = extract_scores_from_result(result)
                if scores and len(scores) == len(new_sorry_keys):
                    for i, key in enumerate(new_sorry_keys):
                        score_cache[key] = scores[i]
                        logger.debug(f"Updated score cache (new): {key} = {scores[i]}")
                elif scores:
                    max_score = max(scores)
                    for key in new_sorry_keys:
                        score_cache[key] = max_score
                        logger.debug(f"Updated score cache (new, max): {key} = {max_score}")
                
                tree.truncate_leaves()
                
                # Clean up scores for proved targets
                current_sorry_keys = {node.key for node in tree.walk_leaves() if node.payload.has_sorry}
                keys_to_delete = [key for key in score_cache if key not in current_sorry_keys]
                for key in keys_to_delete:
                    del score_cache[key]
                    logger.debug(f"Deleted score for proved target: {key}")
                
                logger.info("quickcheck succeeded (tolerable errors)")
                return VerifyResult.CHECK_SUCCESS
            else:
                # Other errors, quickcheck failed
                error_detail = "; ".join(errors[:2])
                logger.warning(f"quickcheck failed: {error_detail}")
                return VerifyResult.CHECK_FAILED
        
        # No errors or is_valid_with_sorry, quickcheck passed
        if result.get("is_valid_with_sorry", False) or not has_error:
            # Extract scores and update cache (only update new sorrys)
            scores = extract_scores_from_result(result)
            if scores and len(scores) == len(new_sorry_keys):
                for i, key in enumerate(new_sorry_keys):
                    score_cache[key] = scores[i]
                    logger.debug(f"Updated score cache (new): {key} = {scores[i]}")
            elif scores:
                max_score = max(scores)
                for key in new_sorry_keys:
                    score_cache[key] = max_score
                    logger.debug(f"Updated score cache (new, max): {key} = {max_score}")
            
            tree.truncate_leaves()
            
            # Clean up scores for proved targets
            current_sorry_keys = {node.key for node in tree.walk_leaves() if node.payload.has_sorry}
            keys_to_delete = [key for key in score_cache if key not in current_sorry_keys]
            for key in keys_to_delete:
                del score_cache[key]
                logger.debug(f"Deleted score for proved target: {key}")
            
            logger.info("quickcheck succeeded")
            return VerifyResult.CHECK_SUCCESS
        
        # Unknown situation
        logger.warning(f"quickcheck unknown error: {result}")
        return VerifyResult.CHECK_FAILED
            
    except RuntimeError as e:
        if "timed out" in str(e) or "timeout" in str(e).lower():
            logger.warning(f"quickcheck timeout: {e}")
            return VerifyResult.CHECK_FAILED
        raise

def check_proof(code: str, cfg: DecomposeConfig) -> dict:
    """Check if the Lean code proof is valid"""
    return verify_lean_code(code, server_url=cfg.lean_server_url, timeout=cfg.timeout)


def recursive_check_proof(
    tree: LeanCodeTree, 
    logger: logging.Logger, 
    cfg: DecomposeConfig,
    score_cache: dict[str, int]
) -> tuple[VerifyResult, str | None]:
    """Recursively check proof - following batch processing version logic
    
    Args:
        tree: Lean code tree
        logger: Logger
        cfg: Configuration
        score_cache: Score cache, updated in place
        
    Returns:
        (Verification result, error message)
    """
    # Step 3: First verify (corresponds to batch_stages Step 3)
    logger.info("Step 3: check the original proof...")
    verify_result = check_proof(tree.to_code(), cfg)
    
    if verify_result.get("is_valid_no_sorry", False):
        logger.info("Step 3: Proof is successful (no sorry)")
        score_cache.clear()  # Fully proved, clear score cache
        return (VerifyResult.PROVE_NO_SORRY, None)
    
    # Revise (corresponds to batch_stages revise_stage)
    try:
        revise_proof(tree, verify_result)
    except Exception as e:
        logger.error(f"Revise proof failed")
        return (VerifyResult.PROVE_FAILED, f"Revise proof failed: {e}")
    
    # Step 4: Re-verify (corresponds to batch_stages Step 4)
    logger.info("Step 4: check the proof with sorry...")
    verify_result = check_proof(tree.to_code(), cfg)
    
    
    if not verify_result.get("is_valid_with_sorry", False):
        error_message = verify_result.get('error_message', [False, []])
        errors = error_message[1] if len(error_message) > 1 and error_message[1] else []
        error_detail = "; ".join(errors[:2]) if errors else "compilation failed"
        logger.error(f"Step 4: Compilation ERROR: {error_message}")
        logger.debug(f"The original code is \n{tree.to_code()}")
        return (VerifyResult.ERROR, error_detail)
    elif not tree.check_target():
        logger.error("Step 4: ORIGINAL THEOREM IS NOT PROVED")
        return (VerifyResult.PROVE_FAILED, "original theorem not proved")
    
    # Step 5: QuickCheck + compute scores (corresponds to batch_stages Step 5/6)
    logger.info("Step 5: check the proof with quickcheck and compute scores...")
    results = check_with_quickcheck(tree, logger, cfg, score_cache)
    return (results, None)
    

def solve_single_problem(problem_id: str, formal_problem: str, logger: logging.Logger, 
                         cfg: DecomposeConfig, max_iterations: int = 10) -> tuple:
    """
    Solve a single problem
    
    Returns:
        (final_result, final_code, success_steps, result_history_dict, iteration_logs)
        iteration_logs: list of input/output records for each iteration
    """
    logger.info(f"Starting problem: {problem_id}")
    logger.info("="*100)
    logger.info(f"Original problem:\n{formal_problem}")
    logger.info("="*100)
    
    # Initialization
    tree = LeanCodeTree(formal_problem)
    result_history = Counter()
    iteration_logs = []  # Store input/output for each iteration
    
    # Initialize score cache: run (countNodesAll; quickcheck) for all initial targets
    score_cache, init_errors = initialize_scores(tree, logger, cfg)
    
    # Save initial score (for final report, aggregated using LogSumExp)
    initial_max_score = calculate_reduction_score(score_cache)
    
    # If compilation errors occurred during initialization (score = -1), return error immediately
    if any(score == -1 for score in score_cache.values()):
        # Collect specific error details
        error_detail = init_errors[0] if init_errors else "unknown compilation error"
        logger.error(f"Compilation error detected during initialization: {error_detail}")
        extra_info = {"initial_score": initial_max_score, "final_score": initial_max_score, "last_error": error_detail}
        return (VerifyResult.ERROR, "", 0, {"error": 1}, [], extra_info)
    
    # Iterative solving
    for iteration in range(max_iterations):
        logger.info(f"\n{'='*50} Iteration {iteration + 1}/{max_iterations} {'='*50}")

        tree.clone("clone_version")
        
        # Log record for current iteration
        iter_log = {
            "iteration": iteration + 1,
            "target_name": None,
            "input_code": None,     # Full code before LLM call
            "input_scores": None,   # score_cache snapshot before LLM call
            "output_code": None,    # Full code after LLM verification
            "output_scores": None,  # score_cache snapshot after LLM verification
            "prompt": None,
            "response": None,
            "thinking": None,  # Store LLM internal thinking
            "result": None,
            "error": None,
        }
                
        try:
            # Select target using softmax probability (without calling Lean server)
            result = select_best_target(tree, score_cache, cfg.target_selection_temperature)
            if result is None:
                logger.info("No targets to prove")
                iter_log["error"] = "No targets to prove"
                iteration_logs.append(iter_log)
                break
            target_name, score = result
            tree.set_target(target_name)  # Set the selected target
            iter_log["target_name"] = target_name
            logger.info(f"Target: {target_name}, cached score: {score}")
        except Exception as e:
            logger.info(f"Error selecting target: {e}")
            iter_log["error"] = f"Error selecting target: {e}"
            iteration_logs.append(iter_log)
            break
        
        # LLM Generate proof
        logger.info("Generate proof...")
        # Save state snapshot before LLM call
        iter_log["input_code"] = tree.to_code()
        iter_log["input_scores"] = dict(score_cache)
        try:
            logger.debug(f"problem: {tree.to_code(target_key=target_name)}")
            proof, prompt, raw_response, thinking = guess_proof(tree, target_name, cfg)
            iter_log["prompt"] = prompt
            iter_log["response"] = raw_response
            iter_log["thinking"] = thinking  # Store thinking content
            logger.debug(f"The proof is \n{proof}")
            logger.info(f"Proof generation complete, length: {len(proof)}")
            if thinking:
                logger.debug(f"Thinking content length: {len(thinking)}")
        except Exception as e:
            logger.error(f"LLM call failed: {e}")
            iter_log["error"] = f"LLM call failed: {e}"
            iteration_logs.append(iter_log)
            result_history[VerifyResult.ERROR] += 1
            continue
        
        # Expand
        logger.info("Expanding proof...")
        try:
            tree.expand(tree.find_node(target_name), proof)
        except Exception as e:
            logger.error(f"Expand failed: {e}")
            logger.error(f"Model response:\n{proof}")
            iter_log["error"] = f"Expand failed: {e}"
            iter_log["result"] = VerifyResult.ERROR.value
            tree.restore("clone_version")
            # Record restored state (same as input_code)
            iter_log["output_code"] = tree.to_code()
            iter_log["output_scores"] = dict(score_cache)
            iteration_logs.append(iter_log)
            result_history[VerifyResult.ERROR] += 1
            continue
        
        # Verify (also compute scores and update cache in Step 5)
        result, error_msg = recursive_check_proof(tree, logger, cfg, score_cache)
        result_history[result] += 1
        iter_log["result"] = result.value
        if error_msg:
            iter_log["error"] = error_msg
        # Save state snapshot after LLM verification
        iter_log["output_code"] = tree.to_code()
        iter_log["output_scores"] = dict(score_cache)
        iteration_logs.append(iter_log)
        logger.info(f"Iteration result: {result.value}")
        
        # Decide next step based on result
        if result == VerifyResult.PROVE_NO_SORRY:
            logger.info(f"Fully proved! {result.value}")
            break
        elif result == VerifyResult.CHECK_SUCCESS:
            # Check if lemma+theorem count exceeds limit
            if cfg.max_lemmas > 0:
                code = tree.to_code()
                num_lemmas = sum(1 for line in code.splitlines()
                                if line.lstrip().startswith(('lemma ', 'theorem ')))
                if num_lemmas > cfg.max_lemmas:
                    logger.warning(f"Early stop: lemma+theorem count {num_lemmas} exceeds limit {cfg.max_lemmas}")
                    break
            logger.info("Current step succeeded, but proof still has gaps, continuing")
        elif result == VerifyResult.PROVE_FAILED:
            logger.warning(f"Current step failed (prove_failed), reason: {result.value}")
            logger.warning(f"Model response:\n{proof}")
            tree.restore("clone_version")
        elif result == VerifyResult.CHECK_FAILED:
            logger.warning(f"Current step failed (check_failed), reason: {result.value}")
            tree.restore("clone_version")
        elif result == VerifyResult.ERROR:
            logger.error(f"Current step compilation error, reason: {result.value}")
            tree.restore("clone_version")
        else:
            logger.error(f"Current step has unknown error: {result.value}")
            tree.restore("clone_version")
    
    # Final result
    final_code = tree.to_code()
    
    # Determine final status (by priority)
    if result_history[VerifyResult.PROVE_NO_SORRY] > 0:
        final_result = VerifyResult.PROVE_NO_SORRY
    elif result_history[VerifyResult.CHECK_SUCCESS] > 0:
        final_result = VerifyResult.CHECK_SUCCESS
    elif result_history[VerifyResult.PROVE_FAILED] > 0:
        final_result = VerifyResult.PROVE_FAILED
    elif result_history[VerifyResult.CHECK_FAILED] > 0:
        final_result = VerifyResult.CHECK_FAILED
    else:
        final_result = VerifyResult.ERROR
    
    logger.info("\n" + "="*100)
    logger.info(f"Final result: {final_result.value}")
    logger.info(f"Result statistics: {dict(result_history)}")
    logger.info("="*100)
    
    # Count successful forward steps (CHECK_SUCCESS means quickcheck succeeded, proof progressed but still has gaps)
    success_steps = result_history[VerifyResult.CHECK_SUCCESS]
    
    # Convert result_history to dict format (using value as key)
    result_history_dict = {result.value: count for result, count in result_history.items() if count > 0}
    
    # Collect extra info: initial score, final score
    # Scores for proved targets have been removed from score_cache, aggregate using LogSumExp
    final_max_score = calculate_reduction_score(score_cache)
    
    # Collect the last error message
    last_error = None
    for log in reversed(iteration_logs):
        if log.get("error"):
            last_error = log["error"]
            break
    
    extra_info = {
        "initial_score": initial_max_score,
        "final_score": final_max_score,
        "last_error": last_error,
    }
    
    return (final_result, final_code, success_steps, result_history_dict, iteration_logs, extra_info)

