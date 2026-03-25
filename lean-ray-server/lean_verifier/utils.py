import re
import hashlib
from typing import List, Tuple
import pandas

def extract_code_header_hash(code: str) -> str:
    """
    Extract header (imports/opens) from code and return its hash.
    This is used for intelligent routing to ensure same imports go to same worker.
    
    Args:
        code: Lean code string
        
    Returns:
        MD5 hash of the header, or "empty" if no header
    """
    lines = code.strip().split('\n')
    header_lines = []
    
    for line in lines:
        stripped = line.strip()
        # Identify import/open statements
        if stripped.startswith('import ') or stripped.startswith('open '):
            header_lines.append(line)
        elif stripped and not stripped.startswith('--'):
            # First non-empty, non-comment, non-import line
            break
    
    header_code = '\n'.join(header_lines)
    
    # Generate hash for header (consistent with LeanREPL._split_code)
    if header_code:
        return hashlib.md5(header_code.encode()).hexdigest()
    else:
        return "empty"


def estimate_task_complexity(code: str) -> float:
    """
    Estimate task complexity based on code characteristics.
    Used for prioritizing task scheduling (complex tasks first to avoid long-tail effects).
    
    Based on empirical analysis of 515 timeout cases vs 100 successful cases:
    - Timeout cases average: 7,078 chars, 27.3 have statements, 9.0 omega calls
    - Success cases average: 1,998 chars, 1.9 have statements, 0.2 omega calls
    
    Key timeout predictors (in order of importance):
    1. omega usage (39.3x difference)
    2. have statement count (14.8x difference)
    3. by nesting depth (7.7x difference)
    4. simp_all usage (47% more frequent in timeouts)
    5. Code length (3.5x difference)
    
    Args:
        code: Lean code string
        
    Returns:
        Complexity score (higher = more complex, likely to timeout)
    """
    lines = code.strip().split('\n')
    code_lower = code.lower()
    
    # Basic metrics
    num_lines = len(lines)
    num_chars = len(code)
    
    # Import cost (expensive to load)
    num_imports = sum(1 for line in lines if line.strip().startswith('import '))
    
    # Proof structure
    num_proofs = sum(1 for line in lines if any(kw in line for kw in ['theorem ', 'lemma ', 'example ']))
    
    # CRITICAL: High-risk tactics that cause timeouts
    # omega: 39.3x more calls in timeout cases (0.2 -> 9.0 calls)
    num_omega = code.count('omega')
    
    # simp_all: 47% more frequent in timeout cases (42% -> 89%)
    num_simp_all = code.count('simp_all')
    
    # have statements: 14.8x more in timeout cases (1.9 -> 27.3)
    num_have = code.count('have h')
    
    # by blocks: 7.7x more in timeout cases (2.7 -> 20.9)
    num_by = code.count(' by')
    
    # Other tactics (moderate risk)
    num_simp = code.count('simp') - num_simp_all  # Don't double count simp_all
    num_aesop = code.count('aesop')
    num_norm_num = code.count('norm_num')
    num_decide = code.count('decide')
    
    # Standard tactics (lower risk)
    num_exact = code.count('exact')
    num_rfl = code.count('rfl')
    num_trivial = code.count('trivial')
    
    # Calculate complexity score with empirically-derived weights
    complexity = (
        # Base complexity
        num_lines * 1.0 +                    # Code length baseline
        num_chars * 0.1 +                    # Character count (3.5x difference)
        num_imports * 5.0 +                  # Imports are expensive (cache loading)
        num_proofs * 3.0 +                   # Each proof adds complexity
        
        # HIGH RISK: Major timeout predictors
        num_omega * 50.0 +                   # ⚠️ CRITICAL: 39.3x difference
        num_have * 15.0 +                    # ⚠️ CRITICAL: 14.8x difference
        num_by * 10.0 +                      # ⚠️ HIGH: 7.7x difference (nesting)
        num_simp_all * 25.0 +                # ⚠️ HIGH: 47% more frequent in timeouts
        
        # MODERATE RISK: Automated tactics
        num_simp * 3.0 +                     # simp is safer than simp_all
        num_aesop * 5.0 +                    # aesop can search extensively
        num_norm_num * 4.0 +                 # norm_num can be expensive
        num_decide * 2.0 +                   # decide is relatively safe
        
        # LOW RISK: Direct proof tactics (success indicators)
        num_exact * 0.5 -                    # exact is fast (slight bonus)
        num_rfl * 0.5 -                      # rfl is fast (slight bonus)
        num_trivial * 0.5                    # trivial is fast (slight bonus)
    )
    
    # Apply thresholds from successful cases (bonuses for good patterns)
    # Success cases: 92% have < 5 have statements
    if num_have < 5:
        complexity *= 0.8  # 20% complexity reduction for simple proofs
    
    # Success cases: 89% don't use omega
    if num_omega == 0:
        complexity *= 0.9  # 10% complexity reduction for avoiding omega
    
    # Success cases: 62% use cases/match for structured proofs
    if 'cases' in code_lower or 'match' in code_lower:
        complexity *= 0.85  # 15% complexity reduction for structured approach
    
    # Penalty for extreme values (non-linear scaling)
    if num_have > 20:
        complexity *= 1.5  # 50% penalty for excessive have statements
    if num_omega > 5:
        complexity *= 2.0  # 100% penalty for excessive omega usage
    if num_by > 15:
        complexity *= 1.3  # 30% penalty for deep nesting
    
    return max(0, complexity)  # Ensure non-negative


def split_proof_header(proof: str) -> tuple[str, str]:
    """
    Splits `proof` into:
    - header: the consecutive `import ...` lines at the beginning of the proof,
              with "import Mathlib." lines removed and "import Mathlib" added if necessary.
    - context: rest of the proof

    Args:
        proof (str): The proof code to split

    Returns:
        tuple[str, str]: The modified header and context of the proof
    """
    proof = proof.strip()
    lines = proof.splitlines()
    header_lines = []
    body_start_index = 0
    mathlib_imported = False

    for i, line in enumerate(lines):
        if line.startswith("import"):
            if line.startswith("import Mathlib."):
                mathlib_imported = True
            else:
                header_lines.append(line)
            body_start_index = i + 1
        else:
            break

    # Add "import Mathlib" at the beginning if any "import Mathlib." was found
    if mathlib_imported:
        header_lines.insert(0, "import Mathlib")

    header = "\n".join(header_lines).strip()
    body = "\n".join(lines[body_start_index:]).strip()

    return header, body


def get_error_msg(response): ...


def parse_messages(messages):
    parsed_messages = []
    for msg in messages:
        severity = msg.get("severity", "info")
        data = msg.get("data", "")
        pos = msg.get("pos", {"line": 0, "column": 0})
        end_pos = msg.get("endPos", {"line": 0, "column": 0})
        parsed_messages.append(
            {"severity": severity, "message": data, "pos": pos, "endPos": end_pos}
        )
    return parsed_messages


def parse_error_message(message):
    match = re.match(r"^(.*?):\n(.*)", message, re.DOTALL)
    if match:
        severity = match.group(1)
        msg = match.group(2)
    else:
        severity = "error"
        msg = message
    return [
        {
            "severity": severity,
            "message": msg,
            "pos": {"line": 0, "column": 0},
            "endPos": {"line": 0, "column": 0},
        }
    ]


def parse_lean_response(response):
    messages = []
    if "messages" in response:
        messages = parse_messages(response.get("messages", []))
    elif "message" in response:
        messages = parse_error_message(response.get("message", ""))

    # TODO: @marco is it ok to filter out unsolved goals?
    # messages = list(filter(lambda x: "unsolved goals" not in x["message"], messages))
    # messages = sorted(messages, key=lambda x: (x["pos"]["line"], x["pos"]["column"]))

    # here if multiple errors on same line it will take last, why not first?
    # line_num_to_message = {(message["pos"]["line"]): message for message in messages}
    # here if multiple errors on same line it will take first
    line_num_to_message = {}
    for message in messages:
        key = message["pos"]["line"]
        if key not in line_num_to_message:
            line_num_to_message[key] = message

    return line_num_to_message


def get_messages_for_lines(messages, start_line, end_line):
    selected_messages = []
    has_error = False
    is_unsolved_goals = False
    for idx in range(start_line, end_line + 1):
        if idx in messages:
            selected_messages.append(messages[idx])
            if messages[idx]["severity"] == "error":
                has_error = True
            if "unsolved goals" in messages[idx]["message"]:
                is_unsolved_goals = True
    return selected_messages, has_error, is_unsolved_goals


def has_error_response(
    feedback: dict, accept_sorry: bool = True, return_error_messages: bool = False
):
    """
    Checks if the Lean feedback contains an error.

    Args:
        feedback: The Lean feedback as a dictionary.
        accept_sorry: Whether to accept "sorry" statements as "not an error".
            By default, "sorry" statements are not considered errors.
        return_error_messages: Whether to return the feedback error messages.
    """
    if "error" in feedback:
        r = (True, [feedback["error"]]) if return_error_messages else True
        return r

    if "stderr" in feedback:
        r = (True, [feedback["stderr"]]) if return_error_messages else True
        return r

    # Check for "message" (singular) - e.g., "Unknown environment." 
    # singular message is systematic-level error, should be treated as error
    if "message" in feedback:
        r = (True, [feedback["message"]]) if return_error_messages else True
        return r

    has_error = False
    error_data_values = []
    sorry_data_values = []
    if "messages" in feedback:
        error_data_values = [
            str(message.get('pos', 'unknown')) + ": " + message["data"]
            for message in feedback.get("messages", [])
            if message.get("severity") == "error"
        ]
        has_error = bool(error_data_values)

        if not accept_sorry:
            warning_data_values = [
                str(message.get('pos', 'unknown')) + ": " + message["data"]
                for message in feedback.get("messages", [])
                if message.get("severity") == "warning"
            ]
            sorry_data_values = [
                warning_data
                for warning_data in warning_data_values
                if "declaration uses 'sorry'" in warning_data
            ]
            has_error = has_error or bool(sorry_data_values)

    if return_error_messages:
        return has_error, error_data_values + sorry_data_values
    else:
        return has_error


def parse_client_response(response: dict):
    """
    Parses the response from the Lean4Client.
    Reponse should be the output of client.Lean4Client.(async_)verify

    Args:
        - response (dict): The response from the Lean4Client.

    Returns:
        - dict: A dictionary containing the following keys:
            - has_error: Whether the response contains an error.
            - is_valid_no_sorry: Whether the response is valid without "sorry" statements.
                this is used for proof verification.
            - is_valid_with_sorry: Whether the response is valid with "sorry.
                this is used for statement verification.
    """
    error_message = response.get("error", None)
    json_response = response.get("response", {})

    error = bool(error_message) or has_error_response(json_response)
    is_valid_no_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=False)
    )
    is_valid_with_sorry = (not bool(error_message)) and (
        not has_error_response(json_response, accept_sorry=True)
    )

    return {
        "has_error": error,
        "is_valid_no_sorry": is_valid_no_sorry,
        "is_valid_with_sorry": is_valid_with_sorry,
        "time": json_response.get("time", None) if json_response else None,
    }


def analyze_sample(lean_feedback: dict):
    error = lean_feedback.get("error", None)
    output = parse_client_response(lean_feedback)

    return {
        "is_valid_no_sorry": output["is_valid_no_sorry"],
        "is_valid_with_sorry": output["is_valid_with_sorry"],
        "has_error": output["has_error"],
        "has_connection_error": bool(error),
        "time": None if error is not None and "timed out" in error else output["time"],
    }


def parse_verification_results(response: List[dict]) -> List[dict]:
    """
    Parse batch verification responses from the LeanREPL
    
    Args:
        response: List of responses from the LeanREPL
        
    Returns:
        List of parsed results with keys: has_error, is_valid_no_sorry, is_valid_with_sorry, time
    """
    results = [parse_client_response(r) for r in response]
    return results


def parse_verification_error_results(response: List[dict]) -> List[tuple]:
    """
    Parse the error results from the LeanREPL's responses
    
    Args:
        response: List of responses from the LeanREPL
        
    Returns:
        List of (has_error, error_messages) tuples
    """
    results = []
    for res in response:
        if "error" in res and res["error"] is not None:
            results.append((True, [res["error"]]))
        else:
            results.append(
                has_error_response(res["response"], return_error_messages=True)
            )
    return results


def analyze(result: List[dict]):
    df = pandas.DataFrame([analyze_sample(sample_result) for sample_result in result])

    # % of proof which compiled and do not contain a sorry.
    valid_rate = df["is_valid_no_sorry"].sum() / len(df)
    print(f"Valid proofs: {100 * valid_rate:.2f} %")

    # Percentage of connection errors.
    connection_error_rate = df["has_connection_error"].sum() / len(df)
    print(f"Connection errors rate: {100 * connection_error_rate:.2f} %")

    # Calculate total verification time (excluding None values which represent timeout error)
    valid_times = df["time"].dropna()
    timeout_count = len(df) - len(valid_times)

    total_time = valid_times.sum()
    print(
        f"Total verification time: {total_time:.2f} seconds (excluding {timeout_count} timeout error)"
    )

    # Also provide average time for reference
    if len(valid_times) > 0:
        avg_time = valid_times.mean()
        print(
            f"Average verification time: {avg_time:.2f} seconds per successful verification"
        )
