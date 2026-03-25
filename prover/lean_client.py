"""Prover Lean client — thin wrapper over common.lean_client.

Adds config-based parameter extraction and prover-specific cheating
detection on top of the unified verification functions.
"""
from __future__ import annotations

import logging
from typing import Dict, List, Tuple, Optional

from prover.config import Config, get_config
from common.lean_client import (
    verify_lean_code as _verify_sync,
    verify_lean_code_async as _verify_async,
    close_async_session,
    check_verification_result,
    extract_unsolved_goals,
    get_sorry_context,
)

logger = logging.getLogger(__name__)


# ---- Re-export for backward compat ----

async def close_aiohttp_session() -> None:
    await close_async_session()


# ---- Config-aware wrappers ----

def _lean_url(config: Config) -> str:
    return config.lean_server.url

def _lean_timeout(config: Config, timeout: int | None) -> int:
    return timeout if timeout is not None else config.lean_server.timeout

def _lean_buffer(config: Config) -> int:
    return config.lean_server.timeout_buffer


def verify_lean_code(
    code: str,
    config: Config = None,
    timeout: int = None,
) -> Dict:
    """Sync Lean verification (delegates to common.lean_client)."""
    if config is None:
        config = get_config()
    return _verify_sync(
        code,
        server_url=_lean_url(config),
        timeout=_lean_timeout(config, timeout),
        timeout_buffer=_lean_buffer(config),
    )


async def verify_lean_code_async(
    code: str,
    config: Config = None,
    timeout: int = None,
) -> Dict:
    """Async Lean verification (delegates to common.lean_client)."""
    if config is None:
        config = get_config()
    return await _verify_async(
        code,
        server_url=_lean_url(config),
        timeout=_lean_timeout(config, timeout),
        timeout_buffer=_lean_buffer(config),
    )


def is_proof_complete(code: str, config: Config = None) -> bool:
    result = verify_lean_code(code, config)
    no_sorry, _, _ = check_verification_result(result)
    return no_sorry


def is_code_compilable(code: str, config: Config = None) -> bool:
    result = verify_lean_code(code, config)
    _, with_sorry, _ = check_verification_result(result)
    return with_sorry


# ============== Anti-cheating detection ==============

import re

# Standard axiom list (these are legitimate Lean/Mathlib axioms)
STANDARD_AXIOMS = {
    'propext',           # Propositional extensionality
    'Quot.sound',        # Quotient type axiom
    'Classical.choice',  # Axiom of choice
    'funext',            # Function extensionality
    'Eq.ndrec',          # Equality elimination
    'rfl',               # Reflexivity
    'sorryAx',           # Axiom used internally by sorry (not cheating, but indicates incomplete proof)
}


def extract_original_theorem_info(original_code: str) -> Tuple[Optional[str], Optional[str], Optional[str], Optional[str]]:
    """
    Extract theorem signature information from original code
    
    Extracts from EVOLVE-BLOCK first; if no EVOLVE-BLOCK, extracts from the entire code.
    
    Args:
        original_code: Original Lean code
        
    Returns:
        (theorem_name, theorem_params, theorem_type, theorem_call_args)
        e.g.: ("Swap_spec_satisfied", 
               "(X: Int) (Y: Int) (h_precond : Swap_precond (X) (Y))",
               "Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond",
               "X Y h_precond")
    """
    # Extract from EVOLVE-BLOCK first
    block_match = re.search(
        r'-- EVOLVE-BLOCK-START\s*([\s\S]*?)\s*-- EVOLVE-BLOCK-END',
        original_code
    )
    
    if block_match:
        search_content = block_match.group(1)
    else:
        # No EVOLVE-BLOCK, search the entire code (for formal_problem)
        search_content = original_code
    
    # Match all theorem declarations: theorem Name ... := by, take the last one
    all_theorems = list(re.finditer(
        r'theorem\s+(\w+)\s*([\s\S]*?)\s*:=\s*by',
        search_content
    ))
    if not all_theorems:
        logger.warning("theorem declaration not found in EVOLVE-BLOCK")
        return None, None, None, None
    theorem_match = all_theorems[-1]
    theorem_name = theorem_match.group(1)
    full_signature = theorem_match.group(2).strip()
    
    # Find the type part after the last : (theorem conclusion)
    # Use parenthesis balancing to find the actual type separator
    paren_depth = 0
    last_colon_pos = -1
    for i, ch in enumerate(full_signature):
        if ch == '(':
            paren_depth += 1
        elif ch == ')':
            paren_depth -= 1
        elif ch == ':' and paren_depth == 0:
            last_colon_pos = i
    
    if last_colon_pos == -1:
        logger.warning("Cannot find type separator in theorem declaration")
        return None, None, None, None
    
    theorem_params = full_signature[:last_colon_pos].strip()
    theorem_type = full_signature[last_colon_pos + 1:].strip()
    
    # Extract call arguments from parameters (strip type annotations)
    # "(X: Int) (Y: Int) (h_precond : ...)" -> "X Y h_precond"
    param_names = re.findall(r'\((\w+)\s*:', theorem_params)
    theorem_call_args = ' '.join(param_names)
    
    return theorem_name, theorem_params, theorem_type, theorem_call_args


def extract_axioms_from_result(result: Dict) -> List[str]:
    """Extract the axiom list from #print axioms output in the verification result"""
    axioms = []
    if 'response' in result and 'response' in result['response']:
        messages = result['response']['response'].get('messages', [])
        for msg in messages:
            if msg.get('severity') == 'info' and 'data' in msg:
                data = msg['data']
                # Format 1: list form [a, b, c]
                list_match = re.search(r'\[([^\]]+)\]', data)
                if list_match:
                    items = list_match.group(1).split(',')
                    axioms.extend([item.strip() for item in items if item.strip()])
                # Format 2: one axiom name per line
                for line in data.split('\n'):
                    line = line.strip()
                    if line and re.match(r'^[A-Za-z_][A-Za-z0-9_\.]*$', line):
                        axioms.append(line)
    return list(set(axioms))


def check_cheating(
    modified_code: str,
    spec_code: str,
    config: Config = None,
) -> Tuple[bool, Optional[str], List[str]]:
    """
    Check if the theorem cheated by modifying the signature or using non-standard axioms
    
    Method:
    1. Extract original theorem signature from spec_code (formal_problem)
    2. Insert verification theorem after EVOLVE-BLOCK-END in modified code
    3. Verification theorem uses the modified theorem to prove the original
    4. If compilation fails, the theorem signature was modified
    5. Check if all used axioms are standard axioms
    
    Args:
        modified_code: Modified code
        spec_code: Code for extracting original theorem signature (formal_problem)
        config: Configuration
        
    Returns:
        (is_cheating, error_message, all_axioms)
    """
    # Extract original theorem signature from spec_code (formal_problem)
    orig_name, orig_params, orig_type, orig_call_args = extract_original_theorem_info(spec_code)
    
    if not orig_name:
        logger.warning("Cannot extract original theorem info, skipping cheating check")
        return False, None, []
    
    # Build verification code: insert original theorem declaration after EVOLVE-BLOCK-END
    verification_code = f"""
-- [Cheating Check] Verify that the theorem in EVOLVE-BLOCK proves the original specification
theorem {orig_name}_original {orig_params} :
    {orig_type} :=
  {orig_name} {orig_call_args}

#print axioms {orig_name}_original
"""
    
    # Insert verification code after EVOLVE-BLOCK-END
    block_end_pattern = re.compile(r'(-- EVOLVE-BLOCK-END)')
    match = block_end_pattern.search(modified_code)
    
    if match:
        insert_pos = match.end()
        check_code = modified_code[:insert_pos] + verification_code + modified_code[insert_pos:]
    else:
        check_code = modified_code + verification_code
    
    # Send to Lean server for verification
    result = verify_lean_code(check_code, config)
    
    # Check if compilation succeeded
    is_valid_no_sorry, is_valid_with_sorry, error_messages = check_verification_result(result)
    
    if not is_valid_with_sorry:
        # Compilation failed = theorem type was changed, cannot prove original theorem
        error_str = "\n".join(error_messages[:3]) if error_messages else "Unknown error"
        return True, f"Theorem signature changed, cannot prove original spec: {error_str}", []
    
    # Compilation succeeded, check axioms
    axioms = extract_axioms_from_result(result)
    
    # Check for non-standard axioms
    cheating_axioms = []
    for axiom in axioms:
        axiom_base = axiom.split('.')[-1] if '.' in axiom else axiom
        if axiom_base not in STANDARD_AXIOMS and axiom not in STANDARD_AXIOMS:
            cheating_axioms.append(axiom)
    
    if cheating_axioms:
        return True, f"Non-standard axioms used: {cheating_axioms}", axioms
    
    return False, None, axioms


async def check_cheating_async(
    modified_code: str,
    spec_code: str,
    config: Config = None,
) -> Tuple[bool, Optional[str], List[str]]:
    """Native async version of check_cheating, using verify_lean_code_async"""
    orig_name, orig_params, orig_type, orig_call_args = extract_original_theorem_info(spec_code)

    if not orig_name:
        logger.warning("Cannot extract original theorem info, skipping cheating check")
        return False, None, []

    verification_code = f"""
-- [Cheating Check] Verify that the theorem in EVOLVE-BLOCK proves the original specification
theorem {orig_name}_original {orig_params} :
    {orig_type} :=
  {orig_name} {orig_call_args}

#print axioms {orig_name}_original
"""

    block_end_pattern = re.compile(r'(-- EVOLVE-BLOCK-END)')
    match = block_end_pattern.search(modified_code)

    if match:
        insert_pos = match.end()
        check_code = modified_code[:insert_pos] + verification_code + modified_code[insert_pos:]
    else:
        check_code = modified_code + verification_code

    result = await verify_lean_code_async(check_code, config)

    is_valid_no_sorry, is_valid_with_sorry, error_messages = check_verification_result(result)

    if not is_valid_with_sorry:
        error_str = "\n".join(error_messages[:3]) if error_messages else "Unknown error"
        return True, f"Theorem signature changed, cannot prove original spec: {error_str}", []

    axioms = extract_axioms_from_result(result)

    cheating_axioms = []
    for axiom in axioms:
        axiom_base = axiom.split('.')[-1] if '.' in axiom else axiom
        if axiom_base not in STANDARD_AXIOMS and axiom not in STANDARD_AXIOMS:
            cheating_axioms.append(axiom)

    if cheating_axioms:
        return True, f"Non-standard axioms used: {cheating_axioms}", axioms

    return False, None, axioms

