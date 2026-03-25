"""
Intermediate transform module - adds EVOLVE-BLOCK markers between decompose output and prove input.

EVOLVE-BLOCK markers restrict the prover to only modify proof bodies (lemma/theorem proof bodies),
preventing changes to import statements and global declarations.
"""

import json
import re
import logging
from typing import List, Dict, Optional
from pathlib import Path

logger = logging.getLogger(__name__)

# Match lemma/theorem declaration lines (proofs only, not def)
THEOREM_PATTERN = re.compile(r'^\s*(theorem|lemma)\s+\w+')

# Match namespace/section end lines (insert EVOLVE-BLOCK-END before end, consistent with best)
END_NAMESPACE_PATTERN = re.compile(r'^\s*end\s+\w+')

# Match import, open, and other top-level declarations that should not be modified
TOP_LEVEL_PATTERN = re.compile(
    r'^\s*(import|open|set_option|universe|variable|namespace|section|attribute|'
    r'instance|class|structure|inductive)\b'
)

EVOLVE_BLOCK_START = "-- EVOLVE-BLOCK-START"
EVOLVE_BLOCK_END = "-- EVOLVE-BLOCK-END"


def add_evolve_block_markers(code: str) -> str:
    """
    Add EVOLVE-BLOCK markers to decompose output code.
    
    Strategy (consistent with decompose_data_best BLOCK placement):
    1. Find the first lemma/theorem declaration line and insert -- EVOLVE-BLOCK-START before it
    2. Insert -- EVOLVE-BLOCK-END before the last "end <namespace>" line (or at end of code if not found)

    If the code already has EVOLVE-BLOCK markers or no lemma/theorem is found, return as-is.

    Args:
        code: Lean code string

    Returns:
        Code with EVOLVE-BLOCK markers added
    """
    if not code or not code.strip():
        return code
    
    # Check if EVOLVE-BLOCK markers already exist
    if "EVOLVE-BLOCK-START" in code:
        return code
    
    lines = code.split("\n")
    
    # Find the first lemma/theorem declaration line
    first_thm_line = None
    for i, line in enumerate(lines):
        if THEOREM_PATTERN.match(line):
            first_thm_line = i
            break
    
    if first_thm_line is None:
        # No lemma/theorem declaration found, skip adding markers
        logger.warning("No lemma/theorem declaration found, skipping EVOLVE-BLOCK markers")
        return code
    
    # Insert START before the first theorem/lemma
    block_lines = lines[first_thm_line:]
    # Find the last "end <namespace>" in the block, insert END before it (consistent with best)
    end_insert_at = None
    for i in range(len(block_lines) - 1, -1, -1):
        if END_NAMESPACE_PATTERN.match(block_lines[i]):
            end_insert_at = i
            break
    if end_insert_at is not None:
        block_with_end = (
            block_lines[:end_insert_at] +
            [EVOLVE_BLOCK_END] +
            block_lines[end_insert_at:]
        )
    else:
        block_with_end = block_lines + [EVOLVE_BLOCK_END]
    
    new_lines = (
        lines[:first_thm_line] +
        [EVOLVE_BLOCK_START] +
        block_with_end
    )
    result = "\n".join(new_lines)
    logger.debug(
        f"Added EVOLVE-BLOCK markers (START before line {first_thm_line + 1}, "
        + ("END before end line" if end_insert_at is not None else "END at end of file")
    )
    return result


def transform_for_prover(data: List[Dict]) -> List[Dict]:
    """
    Transform decompose output into prover input format.

    Main changes:
    1. Add EVOLVE-BLOCK markers to formal_solution
    2. Preserve formal_problem for anti-cheating detection

    Args:
        data: List of decompose output items, each containing:
            - problem_id: Problem ID
            - formal_problem: Original problem definition
            - formal_solution: Decomposed code (may contain sorry)

    Returns:
        Transformed data list compatible with prover input format
    """
    transformed = []
    
    for item in data:
        problem_id = item.get("problem_id", "unknown")
        formal_problem = item.get("formal_problem", "")
        formal_solution = item.get("formal_solution", "")
        
        if not formal_solution:
            if formal_problem:
                logger.info(f"{problem_id}: No formal_solution, using formal_problem instead")
                formal_solution = formal_problem
                item = {**item, "formal_solution": formal_solution}
            else:
                logger.warning(f"Skipping {problem_id}: no formal_solution or formal_problem")
                transformed.append(item)
                continue
        
        # Add EVOLVE-BLOCK markers
        marked_solution = add_evolve_block_markers(formal_solution)
        
        transformed_item = {
            "problem_id": problem_id,
            "formal_problem": formal_problem,
            "formal_solution": marked_solution,
        }
        if "decompose_result" in item:
            transformed_item["decompose_result"] = item["decompose_result"]
        transformed.append(transformed_item)
        
        # Check if there are still sorry statements that need proving
        if "sorry" in marked_solution:
            logger.debug(f"{problem_id}: Contains sorry, needs prover completion")
        else:
            logger.info(f"{problem_id}: No sorry, will be verified directly")
    
    logger.info(f"Transform complete: {len(transformed)} problems")
    return transformed


def transform_file(input_path: str, output_path: str) -> List[Dict]:
    """
    Read decompose output from file, transform, and write to a new file.

    Args:
        input_path: Input JSON file path (decompose output)
        output_path: Output JSON file path (prover input)

    Returns:
        Transformed data list
    """
    with open(input_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    transformed = transform_for_prover(data)
    
    Path(output_path).parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(transformed, f, ensure_ascii=False, indent=2)
    
    logger.info(f"Transform results saved to: {output_path}")
    return transformed
