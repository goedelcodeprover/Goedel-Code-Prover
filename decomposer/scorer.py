"""
Target scoring and selection module

Evaluates complexity based on the number of constants involved in goals,
prioritizing the most complex targets for decomposition.
Scores are computed and cached during the Step 5 quickcheck phase,
and cached scores are used preferentially when selecting targets.
"""
from __future__ import annotations

import re
import math
import random
import logging

from LeanCodeParser import LeanCodeTree

logger = logging.getLogger(__name__)

# Lean code header with constant collection and counting definitions
SCORE_CODE_HEADER = """
import Tacs
"""


def extract_scores_from_result(result: dict) -> list[int]:
    """Extract constant count scores from verification result
    
    Args:
        result: Verification result returned by the Lean server
        
    Returns:
        List of constant count scores
    """
    node_scores = []
    if 'response' in result and 'response' in result['response'] and result['response']['response'] is not None:
        messages = result['response']['response'].get('messages', [])
        for msg in messages:
            if msg.get('severity') == 'info' and 'data' in msg:
                data = msg['data']
                # Match format: CONSTS_COUNT: 90
                match = re.search(r'CONSTS_COUNT:\s*(\d+)', data)
                if match:
                    node_count = int(match.group(1))
                    node_scores.append(node_count)
    else:
      logger.error(f"Error: verification returned None result, details: {result}")
    return node_scores


def calculate_reduction_score(score_dict: dict[str, int]) -> float:
    """Aggregate scores of multiple sorry targets using LogSumExp
    
    LogSumExp(x, T) = T * log(Σ exp(xᵢ / T))
    Approximates max when temperature T is low, but is sensitive to multiple scores near the maximum,
    thereby penalizing cases with many sorrys.
    
    Returns 0 when there are no sorrys (empty dict), indicating a complete proof (best case).
    
    Args:
        score_dict: Target score cache {target_key: score}
        
    Returns:
        Aggregated score, lower is better (0 = fully proved)
    """
    if not score_dict:
        return 0.0
    
    lemma_node_counts = [v for v in score_dict.values() if v >= 0]
    if not lemma_node_counts:
        return 0.0
    
    temperature = 5.0
    scaled = [nc / temperature for nc in lemma_node_counts]
    max_scaled = max(scaled)
    logsumexp = max_scaled + math.log(sum(math.exp(s - max_scaled) for s in scaled))
    effective_max = logsumexp * temperature
    return effective_max


def softmax_probs(scores: list[float], temperature: float = 0.9) -> list[float]:
    """Compute softmax probabilities
    
    Args:
        scores: List of scores
        temperature: Temperature parameter, higher = more uniform distribution, lower = concentrated on high scores
        
    Returns:
        List of probabilities summing to 1
    """
    if temperature <= 0:
        temperature = 1.0
    
    # Scale scores
    scaled = [s / temperature for s in scores]
    # Subtract max to prevent overflow
    max_scaled = max(scaled)
    exp_scores = [math.exp(s - max_scaled) for s in scaled]
    total = sum(exp_scores)
    
    return [e / total for e in exp_scores]


def select_best_target(tree: LeanCodeTree, score_cache: dict[str, int], temperature: float = 1.0) -> tuple[str, int] | None:
    """Select a target by probability
    
    Uses softmax to convert scores into probabilities, then randomly selects a target.
    Temperature controls exploration: higher = more uniform, lower = biased toward high scores.
    
    Cached scores are used preferentially; uncached targets default to score 0.
    Does not call the Lean server; scores are computed during the Step 5 quickcheck phase.
    
    Args:
        tree: Lean code tree
        score_cache: Target score cache {target_key: score}
        temperature: Softmax temperature parameter, default 1.0
        
    Returns:
        If a target is found, returns a (target_key, score) tuple
        Returns None if no targets are available
    """
    # Collect all leaf nodes containing sorry
    candidates: list[tuple[str, int]] = []
    for node in tree.walk_leaves():
        if node.payload.has_sorry:
            target_key = node.key
            # Use cached score, default to 0 if not cached
            score = score_cache.get(target_key, 0)
            candidates.append((target_key, score))
    
    if not candidates:
        return None
    
    # Return directly when there is only one candidate
    if len(candidates) == 1:
        selected_target, selected_score = candidates[0]
        logger.info(f"Selected target: {selected_target} (only candidate, score: {selected_score})")
        return (selected_target, selected_score)
    
    # Compute softmax probabilities
    scores = [c[1] for c in candidates]
    probs = softmax_probs(scores, temperature)
    
    # Randomly select by probability
    selected_idx = random.choices(range(len(candidates)), weights=probs, k=1)[0]
    selected_target, selected_score = candidates[selected_idx]
    
    # Sort by score descending for log display
    sorted_candidates = sorted(zip(candidates, probs), key=lambda x: x[0][1], reverse=True)
    
    logger.info(f"Selected target: {selected_target} (score: {selected_score}, prob: {probs[selected_idx]:.3f}, temp: {temperature})")
    logger.debug(f"All candidate targets and probabilities: {[(c[0], c[1], f'{p:.3f}') for c, p in sorted_candidates]}")
    
    return (selected_target, selected_score)

