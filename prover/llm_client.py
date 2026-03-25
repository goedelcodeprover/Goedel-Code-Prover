"""
LLM client module

Wraps OpenAI / Azure OpenAI API calls with token billing statistics.
"""

import asyncio
import logging
import threading
from typing import List, Dict, Optional, Any

import httpx
import openai

from prover.config import Config, get_config
from common.budget import (
    BudgetExceededError,
    update_usage as _update_usage_stats,
    get_usage_stats as _get_raw_usage_stats,
    check_budget as _check_raw_budget,
    reset_usage_stats,
    print_usage_stats as _print_raw_usage_stats,
)

logger = logging.getLogger(__name__)


# ==================== Token usage statistics (delegated to common.budget) ====================

def _budget_kwargs(config: Config = None) -> dict:
    """Build keyword arguments for budget functions from Config"""
    if config is None:
        config = get_config()
    llm = config.llm
    return dict(
        input_price_per_million=llm.input_token_price,
        output_price_per_million=llm.output_token_price,
        budget_limit=llm.budget_limit,
        model=llm.model,
    )


def get_usage_stats(config: Config = None) -> Dict[str, Any]:
    """Get token usage statistics and estimated costs"""
    return _get_raw_usage_stats(**_budget_kwargs(config))


def check_budget(config: Config = None) -> None:
    """Check if budget is exceeded; raises an exception if so"""
    kw = _budget_kwargs(config)
    kw.pop("model", None)
    _check_raw_budget(**kw)


def print_usage_stats(config: Config = None) -> None:
    """Print token usage statistics"""
    _print_raw_usage_stats(**_budget_kwargs(config))


# System Prompt for proving Lean lemmas (first attempt)
PROVER_SYSTEM_PROMPT = """Lean 4 proof assistant.

Task: Complete the proof by filling in the `sorry` placeholder with valid tactics.

The SEARCH block should match the original code (including whitespace).

**IMPORTANT**: You MUST first output your reasoning in a ```reasoning block before any diff blocks. This is required.

Output format:
```reasoning
your step-by-step analysis here
```

```diff
<<<<<<< SEARCH
code to match
=======
new code
>>>>>>> REPLACE
```

Recommended tactics (try in order):
- grind                    -- powerful automation, try first
- aesop                    -- general automation
- simp_all                 -- aggressive simplification
- omega                    -- linear arithmetic
- decide                   -- decidable propositions
- by_cases h : cond <;> simp_all  -- case split
- induction x <;> simp_all        -- induction"""

# System Prompt for fixing compiler errors (retry attempts)
FIXER_SYSTEM_PROMPT = """Lean 4 proof assistant.

Task: Correct the compilation errors. Avoid using `sorry`.

**IMPORTANT**: You MUST first output your reasoning in a ```reasoning block before any diff blocks. This is required.

Output format:
```reasoning
your step-by-step analysis here
```

```diff
<<<<<<< SEARCH
code to match
=======
new code
>>>>>>> REPLACE
```

Recommended tactics: grind, aesop, simp_all, omega, decide"""

# System Prompt for eliminating errors with sorry (Stage 2)
ELIMINATE_SYSTEM_PROMPT = """Lean 4 syntax helper.

Task: Make the code compile by adding `sorry` where needed.

**IMPORTANT**: You MUST first output your reasoning in a ```reasoning block before any diff blocks. This is required.

Output format:
```reasoning
your step-by-step analysis here
```

```diff
<<<<<<< SEARCH
code to match
=======
new code
>>>>>>> REPLACE
```"""


ELIMINATE_USER_PROMPT_TEMPLATE = """Address the compilation errors below. Keep working code unchanged.

How to address:
- "unsolved goals" error → Append `sorry` after the tactic (e.g., `simp [x]` → `simp [x]; sorry`)
- Other errors (failed to synthesize, type mismatch) → Use `sorry` for the proof body from the error line to the end of that lemma/theorem
- Multiple goals from one tactic → Add multiple `sorry`s as needed

{code}

Errors:

{errors}

Output diff blocks only. Address only the erroring lines, keep everything else unchanged."""


FIX_USER_PROMPT_TEMPLATE = """Correct the compilation errors shown below. Analyze the error messages carefully. Do not use `sorry`.

Common fixes:
- "type mismatch" → Check the types and adjust the expression
- "unknown identifier" → Check spelling or imports
- "failed to synthesize" → Provide the missing instance
- "unsolved goals" → Try a different tactic

{code}

Errors:

{errors}

Output diff blocks only. Correct the errors by adjusting the code, not by adding sorry."""


PROVE_USER_PROMPT_TEMPLATE = """Complete the current proof goal.

Strategy: Use automation tactics to prove the goal directly.

Tips:
- `simp +decide [...]` is better than `simp [...]` (we trust the Lean 4 compiler)
- `grind` and `aesop` are powerful automation tactics, try them aggressively
- Use `omega` for arithmetic goals, `decide` for decidable propositions
- If a direct proof is too hard, try `by_cases` to split into simpler cases

Recommended tactics (try in order):
```lean
grind                                    -- most powerful, try first
aesop                                    -- general automation
simp +decide [relevant_lemmas]           -- simplification with decidability
omega                                    -- linear arithmetic
decide                                   -- decidable propositions
by_cases h : condition <;> simp_all     -- case split
induction x with ... <;> simp_all       -- induction with auto finish
```

Example - completing with induction:
```lean
-- Before: has placeholder
lemma sum_zero (xs : List Nat) : (xs.map (· * 0)).sum = 0 := by sorry

-- After: induction with simp_all finishes each case
lemma sum_zero (xs : List Nat) : (xs.map (· * 0)).sum = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp_all
```

{code}

Goal (Line {line}):

{goal}

Output diff blocks only."""


_client_cache = {}
_client_cache_lock = threading.Lock()


def create_client(config: Config = None):
    """Create or get cached async OpenAI client (thread-safe singleton)

    Returns openai.AsyncOpenAI / AsyncAzureOpenAI for generate_proof to await directly.
    httpx.AsyncClient is only created on cache miss to avoid connection pool leaks during large-scale inference.
    """
    if config is None:
        config = get_config()
    
    llm = config.llm
    prover = getattr(config, "prover", None)
    max_workers = getattr(prover, "max_workers", 512) if prover else 512
    pool_size = min(max(max_workers, 128), 4096)
    timeout_sec = llm.timeout

    cache_key = (llm.api_base, llm.api_key, llm.use_azure_ad, llm.use_v1_api,
                 llm.managed_identity_client_id, llm.api_version, llm.timeout, pool_size)
    
    with _client_cache_lock:
        if cache_key in _client_cache:
            return _client_cache[cache_key]

    http_timeout = httpx.Timeout(timeout_sec, pool=timeout_sec)
    http_limits = httpx.Limits(max_connections=pool_size, max_keepalive_connections=min(500, pool_size))
    async_http_client = httpx.AsyncClient(limits=http_limits, timeout=http_timeout)
    
    if llm.use_azure_ad:
        try:
            from azure.identity import DefaultAzureCredential, get_bearer_token_provider
        except ImportError:
            raise ImportError(
                "Azure identity libraries required. Install with: pip install azure-identity"
            )
        
        credential = DefaultAzureCredential(
            managed_identity_client_id=llm.managed_identity_client_id
        )
        
        if llm.use_v1_api:
            token_provider = get_bearer_token_provider(
                credential, "https://cognitiveservices.azure.com/.default"
            )
            token = token_provider()
            client = openai.AsyncOpenAI(
                api_key=token,
                base_url=llm.api_base,
                timeout=timeout_sec,
                http_client=async_http_client,
            )
        else:
            token_provider = get_bearer_token_provider(
                credential, "https://cognitiveservices.azure.com/.default"
            )
            client = openai.AsyncAzureOpenAI(
                azure_endpoint=llm.api_base,
                azure_ad_token_provider=token_provider,
                api_version=llm.api_version,
                timeout=timeout_sec,
                http_client=async_http_client,
            )
    else:
        client = openai.AsyncOpenAI(
            api_key=llm.api_key,
            base_url=llm.api_base if llm.api_base else None,
            timeout=timeout_sec,
            http_client=async_http_client,
        )
    
    with _client_cache_lock:
        if cache_key in _client_cache:
            # Another thread cached the client while we were creating it; close our redundant resources
            try:
                import asyncio
                loop = asyncio.get_event_loop()
                if loop.is_running():
                    loop.create_task(async_http_client.aclose())
                else:
                    asyncio.run(async_http_client.aclose())
            except Exception:
                pass
            return _client_cache[cache_key]
        _client_cache[cache_key] = client
    
    return client


async def generate_proof(
    code: str,
    goal_info: Dict,
    config: Config = None,
    error_messages: str = "",
    strategy: str = "prove",
) -> Dict:
    """
    Call LLM to generate proof
    
    Args:
        code: Current Lean code
        goal_info: Goal information, containing line, goal, full_goal
        config: Configuration
        error_messages: Compiler error messages
        strategy: Strategy type
            - "prove": First proof of sorry (no errors)
            - "fix": Fix compilation errors (real fix, no sorry)
            - "eliminate": Eliminate errors using sorry
        
    Returns:
        Dict with complete information:
        {
            "system_prompt": str,
            "user_prompt": str,
            "model": str,
            "response": str,
            "strategy": str,
        }
    """
    if config is None:
        config = get_config()
    
    client = create_client(config)
    
    # Select prompt based on strategy
    if strategy == "eliminate":
        # Eliminate mode: eliminate errors with sorry
        system_prompt = ELIMINATE_SYSTEM_PROMPT
        user_message = ELIMINATE_USER_PROMPT_TEMPLATE.format(
            code=f"```lean\n{code}\n```",
            errors=error_messages,
        )
    elif strategy == "fix" and error_messages:
        # Fix mode: actually fix errors
        system_prompt = FIXER_SYSTEM_PROMPT
        user_message = FIX_USER_PROMPT_TEMPLATE.format(
            code=f"```lean\n{code}\n```",
            errors=error_messages,
        )
    else:
        # Prove mode: first proof of sorry
        system_prompt = PROVER_SYSTEM_PROMPT
        user_message = PROVE_USER_PROMPT_TEMPLATE.format(
            code=f"```lean\n{code}\n```",
            line=goal_info.get('line', '?'),
            goal=goal_info.get('full_goal', goal_info.get('goal', '')),
        )

    # Get model name (strip azure- prefix)
    model = config.llm.model
    if model.lower().startswith("azure-"):
        model = model.split("azure-", 1)[-1]
    
    # Check if this is a reasoning model
    REASONING_MODEL_PREFIXES = (
        "o1-", "o1", "o3-", "o3", "o4-",
        "gpt-5-", "gpt-5", "gpt-oss-",
    )
    is_reasoning_model = model.lower().startswith(REASONING_MODEL_PREFIXES)
    
    # Build request parameters
    if is_reasoning_model:
        api_params = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_message},
            ],
            "max_completion_tokens": config.llm.max_tokens,
        }
    else:
        api_params = {
            "model": model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_message},
            ],
            "temperature": config.llm.temperature,
            "max_tokens": config.llm.max_tokens,
        }
    
    try:
        # Native async call, no longer needs run_in_executor
        if "codex" in model.lower():
            response = await client.responses.create(
                model=model,
                input=user_message,
                instructions=system_prompt,
            )
            result = response.output[1].content[0].text
            logger.debug(f"[LLM] Responses API model: {model}")
        else:
            response = await client.chat.completions.create(**api_params)
            msg = response.choices[0].message
            result = msg.content
            # Some reasoning models put the body in model_extra.reasoning, content is None
            if result is None and getattr(msg, "model_extra", None) and isinstance(msg.model_extra, dict):
                result = msg.model_extra.get("reasoning") or msg.model_extra.get("content")
            if result is None:
                result = ""
        
        # Update token usage statistics
        if hasattr(response, 'usage') and response.usage:
            _update_usage_stats(response.usage)
        
        # Check if budget is exceeded
        check_budget(config)
        
        if config.debug:
            logger.debug(f"[LLM] Response:\n{result}")
        
        return {
            "system_prompt": system_prompt,
            "user_prompt": user_message,
            "model": model,
            "response": result,
            "strategy": strategy,
        }
        
    except BudgetExceededError:
        # Budget exceeded, propagate upward
        raise
    except Exception as e:
        logger.error(f"[LLM] API call failed: {type(e).__name__}: {e}")
        raise


def generate_proof_sync(
    code: str,
    goal_info: Dict,
    config: Config = None,
    error_messages: str = "",
    strategy: str = "prove",
) -> Dict:
    """
    Synchronous version of generate_proof
    """
    return asyncio.run(generate_proof(code, goal_info, config, error_messages, strategy))

