"""
Diff utilities module

Handles code replacement in SEARCH/REPLACE format.
"""

import difflib
import re
from typing import List, Optional, Tuple


# SEARCH/REPLACE regex pattern
DIFF_PATTERN = r"<<<<<<< SEARCH\n(.*?)=======\n(.*?)>>>>>>> REPLACE"

# EVOLVE-BLOCK marker pattern (supports --, #, // comment styles)
EVOLVE_BLOCK_START_PATTERN = re.compile(r'^\s*(--|#|//)\s*EVOLVE-BLOCK-START')
EVOLVE_BLOCK_END_PATTERN = re.compile(r'^\s*(--|#|//)\s*EVOLVE-BLOCK-END')


def extract_diffs(
    diff_text: str, 
    diff_pattern: str = DIFF_PATTERN
) -> List[Tuple[str, str]]:
    """
    Extract diff blocks from text
    
    Args:
        diff_text: Text containing SEARCH/REPLACE format
        diff_pattern: Regex pattern
        
    Returns:
        List of (search_text, replace_text) tuples
    """
    diff_blocks = re.findall(diff_pattern, diff_text, re.DOTALL)
    return [(match[0].rstrip(), match[1].rstrip()) for match in diff_blocks]


def apply_diff(
    original_code: str,
    diff_text: str,
    diff_pattern: str = DIFF_PATTERN,
) -> Tuple[str, bool, List[dict]]:
    """
    Apply a diff to the original code with robust matching and status reporting.
    
    Matching strategies (tried in order):
    1. Exact match
    2. Trailing whitespace stripped
    3. All whitespace normalized (multiple spaces -> single space)
    4. Fuzzy match with first+last lines anchor

    Args:
        original_code: Original source code
        diff_text: Diff in the SEARCH/REPLACE format
        diff_pattern: Regex pattern for the SEARCH/REPLACE format

    Returns:
        Tuple of (modified_code, all_applied, block_results)
        - modified_code: The resulting code after applying diffs
        - all_applied: True if all diff blocks were successfully applied
        - block_results: List of dicts with details for each block
    """
    result_lines = original_code.split("\n")
    diff_blocks = extract_diffs(diff_text, diff_pattern)
    
    block_results = []

    for search_text, replace_text in diff_blocks:
        search_lines = search_text.split("\n")
        replace_lines = replace_text.split("\n")
        
        result = _try_apply_single_diff(result_lines, search_lines, replace_lines)
        block_results.append(result)
        
        if result["applied"]:
            result_lines = result["new_lines"]
    
    all_applied = all(r["applied"] for r in block_results) if block_results else False
    
    return "\n".join(result_lines), all_applied, block_results


def _try_apply_single_diff(
    result_lines: List[str],
    search_lines: List[str],
    replace_lines: List[str],
) -> dict:
    """
    Try to apply a single diff block using multiple matching strategies.
    """
    search_preview = search_lines[0][:50] if search_lines else ""
    
    # Strategy 1: Exact match
    match_line = _find_exact_match(result_lines, search_lines)
    if match_line is not None:
        new_lines = result_lines[:match_line] + replace_lines + result_lines[match_line + len(search_lines):]
        return {
            "applied": True,
            "match_strategy": "exact",
            "search_preview": search_preview,
            "match_line": match_line,
            "new_lines": new_lines,
        }
    
    # Strategy 2: Trailing whitespace stripped
    match_line = _find_match_stripped(result_lines, search_lines)
    if match_line is not None:
        new_lines = result_lines[:match_line] + replace_lines + result_lines[match_line + len(search_lines):]
        return {
            "applied": True,
            "match_strategy": "trailing_whitespace_stripped",
            "search_preview": search_preview,
            "match_line": match_line,
            "new_lines": new_lines,
        }
    
    # Strategy 3: Normalize all whitespace
    match_line = _find_match_normalized(result_lines, search_lines)
    if match_line is not None:
        new_lines = result_lines[:match_line] + replace_lines + result_lines[match_line + len(search_lines):]
        return {
            "applied": True,
            "match_strategy": "whitespace_normalized",
            "search_preview": search_preview,
            "match_line": match_line,
            "new_lines": new_lines,
        }
    
    # Strategy 4: Fuzzy match
    match_line, match_len = _find_match_fuzzy(result_lines, search_lines)
    if match_line is not None:
        new_lines = result_lines[:match_line] + replace_lines + result_lines[match_line + match_len:]
        return {
            "applied": True,
            "match_strategy": "fuzzy_anchor",
            "search_preview": search_preview,
            "match_line": match_line,
            "new_lines": new_lines,
        }
    
    # No match found
    return {
        "applied": False,
        "match_strategy": None,
        "search_preview": search_preview,
        "match_line": None,
        "new_lines": result_lines,
    }


def _find_exact_match(result_lines: List[str], search_lines: List[str]) -> Optional[int]:
    """Find exact match, return starting line index or None."""
    for i in range(len(result_lines) - len(search_lines) + 1):
        if result_lines[i : i + len(search_lines)] == search_lines:
            return i
    return None


def _find_match_stripped(result_lines: List[str], search_lines: List[str]) -> Optional[int]:
    """Find match with trailing whitespace stripped."""
    result_stripped = [line.rstrip() for line in result_lines]
    search_stripped = [line.rstrip() for line in search_lines]
    
    for i in range(len(result_stripped) - len(search_stripped) + 1):
        if result_stripped[i : i + len(search_stripped)] == search_stripped:
            return i
    return None


def _find_match_normalized(result_lines: List[str], search_lines: List[str]) -> Optional[int]:
    """Find match with all whitespace normalized."""
    def normalize(line: str) -> str:
        return ' '.join(line.split())
    
    result_norm = [normalize(line) for line in result_lines]
    search_norm = [normalize(line) for line in search_lines]
    
    for i in range(len(result_norm) - len(search_norm) + 1):
        if result_norm[i : i + len(search_norm)] == search_norm:
            return i
    return None


def _find_match_fuzzy(
    result_lines: List[str], 
    search_lines: List[str]
) -> Tuple[Optional[int], Optional[int]]:
    """
    Fuzzy match: anchor on first and last non-empty lines of search.
    Returns (start_line, length) or (None, None).
    """
    # Get first and last non-empty lines from search
    first_idx = None
    last_idx = None
    for i, line in enumerate(search_lines):
        if line.strip():
            if first_idx is None:
                first_idx = i
            last_idx = i
    
    if first_idx is None:
        return None, None
    
    first_line = search_lines[first_idx].rstrip()
    last_line = search_lines[last_idx].rstrip()
    expected_span = last_idx - first_idx + 1
    
    # Find in result
    for i in range(len(result_lines)):
        if result_lines[i].rstrip() == first_line:
            # Check if last line matches at expected distance
            end_idx = i + expected_span - 1
            if end_idx < len(result_lines) and result_lines[end_idx].rstrip() == last_line:
                # Verify middle lines roughly match
                middle_match = True
                for j in range(first_idx + 1, last_idx):
                    result_j = i + (j - first_idx)
                    if result_j >= len(result_lines):
                        middle_match = False
                        break
                    if ' '.join(search_lines[j].split()) != ' '.join(result_lines[result_j].split()):
                        middle_match = False
                        break
                
                if middle_match:
                    actual_len = len(search_lines)
                    return i, actual_len
    
    return None, None


def parse_code_block(llm_response: str, language: str = "lean") -> Optional[str]:
    """
    Extract code block from LLM response
    
    Args:
        llm_response: LLM response text
        language: Programming language
        
    Returns:
        Extracted code, or None
    """
    # Try to match code block for the specified language
    pattern = r"```" + language + r"\n(.*?)```"
    matches = re.findall(pattern, llm_response, re.DOTALL)
    
    if matches:
        return matches[0].strip()
    
    # Fallback: any code block
    pattern = r"```(.*?)```"
    matches = re.findall(pattern, llm_response, re.DOTALL)
    
    if matches:
        return matches[0].strip()
    
    return None


def restore_evolve_block_markers(original_code: str, modified_code: str) -> str:
    """
    Post-processing: if the model output removed EVOLVE-BLOCK markers, restore them automatically.
    
    - Missing EVOLVE-BLOCK-START: insert before the first lemma/theorem declaration
    - Missing EVOLVE-BLOCK-END: insert after the last lemma/theorem proof block
    
    Args:
        original_code: Original code (with complete EVOLVE-BLOCK markers)
        modified_code: Code after applying diff
        
    Returns:
        Repaired code (if repair was needed)
    """
    # Original code must have a complete EVOLVE-BLOCK range
    orig_range = parse_evolve_block_range(original_code)
    if orig_range is None:
        return modified_code
    
    mod_lines = modified_code.split("\n")
    has_start = any(EVOLVE_BLOCK_START_PATTERN.match(line) for line in mod_lines)
    has_end = any(EVOLVE_BLOCK_END_PATTERN.match(line) for line in mod_lines)
    
    if has_start and has_end:
        return modified_code
    
    # Get marker lines verbatim from original code
    orig_lines = original_code.split("\n")
    start_idx, end_idx = orig_range
    start_marker = orig_lines[start_idx]
    end_marker = orig_lines[end_idx]
    
    # Find all lemma/theorem declaration lines in modified code
    thm_pattern = re.compile(r'^\s*(theorem|lemma)\s+\w+')
    thm_lines = [i for i, line in enumerate(mod_lines) if thm_pattern.match(line)]
    
    if not thm_lines:
        return modified_code
    
    # Process END first (inserting at the back does not affect earlier line numbers)
    if not has_end:
        last_thm = thm_lines[-1]
        
        # Scan downward from the last theorem/lemma to find the end of the proof block
        # Encountering a top-level construct (end/def/namespace etc.) means the proof block has ended
        top_level = re.compile(
            r'^(end|def|namespace|section|class|instance|structure|'
            r'inductive|open|variable|set_option|import|#)\b'
        )
        
        insert_pos = len(mod_lines)
        for i in range(last_thm + 1, len(mod_lines)):
            if mod_lines[i].strip() and top_level.match(mod_lines[i]):
                insert_pos = i
                break
        
        mod_lines.insert(insert_pos, end_marker)
    
    # Then process START (inserting at the front)
    if not has_start:
        # Re-find thm_lines since inserting END may have changed line numbers (but END is after, so front indices are unaffected)
        first_thm = thm_lines[0]
        mod_lines.insert(first_thm, "")
        mod_lines.insert(first_thm, start_marker)
    
    return "\n".join(mod_lines)


def parse_evolve_block_range(code: str) -> Optional[Tuple[int, int]]:
    """
    Parse the EVOLVE-BLOCK line number range in code
    
    Args:
        code: Source code
        
    Returns:
        (start_line, end_line) tuple (0-indexed), or None if markers are not found
    """
    lines = code.split("\n")
    start_line = None
    end_line = None
    
    for i, line in enumerate(lines):
        if EVOLVE_BLOCK_START_PATTERN.match(line):
            start_line = i
        elif EVOLVE_BLOCK_END_PATTERN.match(line):
            end_line = i
    
    if start_line is not None and end_line is not None and start_line < end_line:
        return (start_line, end_line)
    
    return None


def validate_changes_within_evolve_block(
    original_code: str,
    modified_code: str,
) -> Tuple[bool, Optional[str]]:
    """
    Validate that all changes are within the EVOLVE-BLOCK range
    
    Args:
        original_code: Original code (containing EVOLVE-BLOCK markers)
        modified_code: Modified code
        
    Returns:
        (is_valid, error_message)
        - is_valid: True if all changes are within the EVOLVE-BLOCK
        - error_message: Error description if validation fails
    """
    # Parse EVOLVE-BLOCK range
    block_range = parse_evolve_block_range(original_code)
    
    if block_range is None:
        # No EVOLVE-BLOCK markers, allow all modifications
        return True, None
    
    start_line, end_line = block_range
    
    def is_line_in_allowed_range(line_num: int) -> bool:
        """Check if the line number is within the allowed modification range (including marker lines)"""
        return start_line <= line_num <= end_line
    
    # Compare original code and modified code
    original_lines = original_code.split("\n")
    modified_lines = modified_code.split("\n")
    
    # Use difflib to find changes
    violations = []
    matcher = difflib.SequenceMatcher(None, original_lines, modified_lines)
    
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == 'equal':
            continue
        
        # For 'replace' and 'delete' operations, check the modified original lines
        if tag in ('replace', 'delete'):
            for line_num in range(i1, i2):
                if not is_line_in_allowed_range(line_num):
                    line_content = original_lines[line_num] if line_num < len(original_lines) else ""
                    violations.append(
                        f"Line {line_num + 1} modified outside EVOLVE-BLOCK: {line_content[:60]}..."
                    )
        
        # For 'insert' operations, check if the insertion point is within the allowed range
        if tag == 'insert':
            insert_point = i1
            # Insertion point must be inside the EVOLVE-BLOCK
            if not is_line_in_allowed_range(insert_point) and not is_line_in_allowed_range(insert_point - 1):
                violations.append(
                    f"Code inserted at line {insert_point + 1} outside EVOLVE-BLOCK"
                )
    
    if violations:
        error_msg = "Changes outside EVOLVE-BLOCK range:\n" + "\n".join(violations[:5])
        if len(violations) > 5:
            error_msg += f"\n... and {len(violations) - 5} other violation(s)"
        return False, error_msg
    
    return True, None

