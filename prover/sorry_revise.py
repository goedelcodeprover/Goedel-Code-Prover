"""
Sorry hard-replace module

Replaces the proof of a failed-to-compile lemma/theorem with sorry so that the code can compile.
This is the fallback when LLM repair fails (Stage 3).
"""

import re
import logging
from typing import Tuple, List, Optional

from common.constants import LEAN_REPL_LINE_OFFSET

logger = logging.getLogger(__name__)


def find_all_theorems(code: str) -> List[Tuple[str, int, int]]:
    """
    Find all lemma/theorem declarations in the code
    
    Returns:
        [(name, start_line, by_line), ...]
        - name: Theorem name
        - start_line: Line number where the declaration starts (0-indexed)
        - by_line: Line number where := by appears (0-indexed)
    """
    lines = code.split('\n')
    theorems = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        # Match lemma or theorem declaration
        match = re.match(r'^\s*(lemma|theorem)\s+(\w+)', line)
        if match:
            name = match.group(2)
            start_line = i
            # Find the position of := by
            by_line = None
            for j in range(i, min(i + 30, len(lines))):
                if ':= by' in lines[j] or ':=by' in lines[j]:
                    by_line = j
                    break
            if by_line is not None:
                theorems.append((name, start_line, by_line))
        i += 1
    
    return theorems


def find_theorem_containing_line(
    code: str, 
    error_line: int, 
    theorems: List[Tuple[str, int, int]] = None
) -> Optional[str]:
    """
    Find the lemma/theorem containing the error line
    
    Args:
        code: Lean code
        error_line: Error line number (1-indexed)
        theorems: Pre-computed theorem list
        
    Returns:
        Found lemma/theorem name, or None
    """
    if theorems is None:
        theorems = find_all_theorems(code)
    
    error_idx = error_line - 1  # Convert to 0-indexed
    
    # Find the theorem containing this line
    for i, (name, start_line, by_line) in enumerate(theorems):
        if i + 1 < len(theorems):
            next_start = theorems[i + 1][1]
        else:
            next_start = len(code.split('\n'))
        
        if start_line <= error_idx < next_start:
            return name
    
    return None


def find_theorem_at_line(code: str, error_line: int) -> Optional[str]:
    """
    Search upward from the error line for the nearest lemma/theorem name
    
    Args:
        code: Lean code
        error_line: Error line number (1-indexed)
        
    Returns:
        Found lemma/theorem name, or None
    """
    lines = code.split('\n')
    # Search upward from the error line
    for i in range(min(error_line - 1, len(lines) - 1), -1, -1):
        line = lines[i]
        # Match lemma or theorem declaration (at line start, possibly with spaces)
        match = re.match(r'^\s*(lemma|theorem)\s+(\w+)', line)
        if match:
            return match.group(2)
        # Also check inline declarations (may have comments before)
        match = re.search(r'\b(lemma|theorem)\s+(\w+)', line)
        if match and not line.strip().startswith('--') and not line.strip().startswith('/-'):
            return match.group(2)
    return None


def extract_error_lines(error_messages: List[str], line_offset: int = 0) -> List[int]:
    """
    Extract line numbers from error message list
    
    Args:
        error_messages: Error message list
        line_offset: Line number offset
        
    Returns:
        Line number list (with offset applied)
    """
    lines = []
    for msg in error_messages:
        if not msg:
            continue
        # Match {'line': N, ...} format
        match = re.search(r"\{'line':\s*(\d+)", str(msg))
        if match:
            lines.append(int(match.group(1)) + line_offset)
    return lines


def replace_proof_with_sorry(code: str, theorem_name: str) -> Tuple[str, bool]:
    """
    Replace the proof of the specified lemma/theorem with sorry
    
    Args:
        code: Lean code
        theorem_name: lemma/theorem name
        
    Returns:
        (new_code, success)
    """
    lines = code.split('\n')
    
    # Find the starting line of the theorem/lemma declaration
    decl_start_idx = None
    for i, line in enumerate(lines):
        if re.match(rf'^(lemma|theorem)\s+{re.escape(theorem_name)}\b', line):
            decl_start_idx = i
            break
    
    if decl_start_idx is None:
        return code, False
    
    # Find the position of := by
    by_line_idx = None
    for i in range(decl_start_idx, min(decl_start_idx + 20, len(lines))):
        if ':= by' in lines[i] or ':=by' in lines[i]:
            by_line_idx = i
            break
        # Also handle the case where := by is split across two lines
        if i > decl_start_idx and lines[i].strip().startswith('by') and ':=' in lines[i-1]:
            by_line_idx = i
            break
    
    if by_line_idx is None:
        return code, False
    
    # Find the end line of the proof
    proof_end_idx = len(lines)
    for i in range(by_line_idx + 1, len(lines)):
        line = lines[i]
        # Check if this is a new top-level declaration
        if re.match(r'^(lemma|theorem|def|axiom|instance|class|structure|inductive|namespace|end|section|#|/-)', line):
            proof_end_idx = i
            break
    
    # Build new code
    decl_lines = lines[decl_start_idx:by_line_idx + 1]
    
    # Process the := by line
    last_decl_line = decl_lines[-1]
    by_pos = last_decl_line.find(':= by')
    if by_pos != -1:
        decl_lines[-1] = last_decl_line[:by_pos + 5]  # ':= by' = 5 chars
    else:
        by_pos = last_decl_line.find(':=by')
        if by_pos != -1:
            decl_lines[-1] = last_decl_line[:by_pos + 4]  # ':=by' = 4 chars
    
    # Assemble new code
    new_lines = (
        lines[:decl_start_idx] +
        decl_lines +
        ['  sorry'] +
        [''] +
        lines[proof_end_idx:]
    )
    
    return '\n'.join(new_lines), True


def sorry_revise(code: str, error_messages: List[str]) -> Tuple[str, bool, List[str]]:
    """
    Fix failed-to-compile code by replacing proofs with sorry
    
    Replaces the proof of erroring lemma/theorem with sorry.
    
    Args:
        code: Original Lean code
        error_messages: Error message list
        
    Returns:
        (revised_code, success, revised_names)
        - revised_code: Repaired code
        - success: Whether replacement was successful
        - revised_names: List of replaced theorem names
    """
    if not error_messages:
        return code, False, []
    
    # Extract error line numbers (Lean Server has a 2-line offset)
    error_lines = extract_error_lines(error_messages, line_offset=LEAN_REPL_LINE_OFFSET)
    if not error_lines:
        return code, False, []
    
    # Pre-compute all theorems
    theorems = find_all_theorems(code)
    
    # Find the lemma/theorem names that need repair
    names_to_revise = set()
    for line in error_lines:
        name = find_theorem_containing_line(code, line, theorems)
        if not name:
            name = find_theorem_at_line(code, line)
        if name:
            names_to_revise.add(name)
    
    if not names_to_revise:
        return code, False, []
    
    # Replace proofs one by one
    revised_code = code
    revised_names = []
    
    for name in names_to_revise:
        new_code, success = replace_proof_with_sorry(revised_code, name)
        if success:
            revised_code = new_code
            revised_names.append(name)
            logger.info(f"  [Sorry Replace] Replaced {name} proof with sorry")
    
    return revised_code, len(revised_names) > 0, revised_names

