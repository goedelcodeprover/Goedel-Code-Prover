"""Utility module - configuration management, LLM calls, logging, result statistics, etc."""
from __future__ import annotations

import logging
import re
import threading
from typing import Any
from enum import Enum

import httpx
import openai
from openai import OpenAI

from decomposer.config import DecomposeConfig
from LeanCodeParser import extract_lean4_code
from common.budget import (
    BudgetExceededError,
    update_usage,
    get_usage_stats as _get_raw_usage_stats,
    check_budget as _check_raw_budget,
    reset_usage_stats,
    print_usage_stats as _print_raw_usage_stats,
)
from common.logger import setup_problem_logger, cleanup_logger  # noqa: F401

try:
    from azure.identity import DefaultAzureCredential, get_bearer_token_provider
    AZURE_IDENTITY_AVAILABLE = True
except ImportError:
    AZURE_IDENTITY_AVAILABLE = False

logger = logging.getLogger(__name__)

# Global configuration
_config: DecomposeConfig | None = None
_openai_client: OpenAI | openai.AzureOpenAI | None = None
_is_azure_client: bool = False
_is_gemini_client: bool = False
_client_lock = threading.Lock()

# Constants
TIMEOUT_BUFFER = 600
MAX_RETRIES = 3
INITIAL_RETRY_DELAY = 1.0
RETRY_BACKOFF_MULTIPLIER = 2


def set_config(cfg: DecomposeConfig) -> None:
    """Set global configuration"""
    global _config, _openai_client
    _config = cfg
    _openai_client = None


def _budget_kwargs() -> dict:
    """Build keyword arguments for budget functions from the current DecomposeConfig"""
    cfg = get_config()
    return dict(
        input_price_per_million=cfg.input_token_price,
        output_price_per_million=cfg.output_token_price,
        budget_limit=cfg.budget_limit,
        model=cfg.model,
    )


def get_usage_stats() -> dict[str, Any]:
    """Get token usage statistics and estimated cost"""
    return _get_raw_usage_stats(**_budget_kwargs())


def check_budget() -> None:
    """Check if the budget has been exceeded, raises an exception if so"""
    kw = _budget_kwargs()
    kw.pop("model", None)
    _check_raw_budget(**kw)


def print_usage_stats() -> None:
    """Print token usage statistics"""
    _print_raw_usage_stats(**_budget_kwargs())


def get_config() -> DecomposeConfig:
    """Get global configuration"""
    global _config
    if _config is None:
        _config = DecomposeConfig()
    return _config


class VerifyResult(Enum):
    """Verification result"""
    PROVE_NO_SORRY = "prove_no_sorry"        # Proof fully successful, no sorry
    PROVE_FAILED = "prove_theorem_failed"    # Proof failed (original theorem not proved)
    CHECK_SUCCESS = "quickcheck_success"     # QuickCheck verification succeeded
    CHECK_FAILED = "quickcheck_failed"       # QuickCheck verification failed
    ERROR = "error"                          # Compilation error


_CATEGORY_RULES = {
    "prove_no_sorry": "Success",
    "prove_with_grind": "Success",
    "prove_with_sorry": "Forward",
    "quickcheck_success": "Forward",
    "quickcheck_unknown": "Fallback",
    "prove_theorem_failed": "Fallback",
    "quickcheck_failed": "Fallback",
    "error": "Error",
    "unknown": "Error",
}


def summarize_categories(result_counter: dict[Any, int]) -> dict[str, int]:
    """Summarize result categories"""
    summary = {"Success": 0, "Forward": 0, "Fallback": 0, "Error": 0}
    for key, count in result_counter.items():
        if count:
            result_key = getattr(key, "value", key)
            category = _CATEGORY_RULES.get(result_key, "Error")
            summary[category] += count
    return summary


def setup_logger(problem_id: str, log_dir: str = "logs") -> logging.Logger:
    """Create problem logger (delegated to common.logger)"""
    return setup_problem_logger(problem_id, log_dir, prefix="decompose")


def get_openai_client() -> OpenAI | openai.AzureOpenAI:
    """Get OpenAI client (supports Azure OpenAI), thread-safe"""
    global _openai_client, _is_azure_client
    
    # Double-checked locking to avoid acquiring the lock on every call
    if _openai_client is not None:
        return _openai_client
    
    with _client_lock:
        # Check again to prevent re-initialization by another thread while waiting for lock
        if _openai_client is not None:
            return _openai_client
        
        cfg = get_config()
        timeout = cfg.timeout + TIMEOUT_BUFFER
        pool_size = min(max(cfg.max_workers, 128), 512)
        
        is_azure = cfg.api_base and ".azure.com" in cfg.api_base.lower()
        _is_azure_client = is_azure  # Update global flag
        
        global _is_gemini_client
        is_gemini = cfg.api_base and "googleapis.com" in cfg.api_base.lower()
        _is_gemini_client = is_gemini  # Update global flag
        
        if is_azure:
            if not AZURE_IDENTITY_AVAILABLE:
                raise ImportError(
                    "Azure identity libraries not available. "
                    "Install with: pip install azure-identity"
                )
            
            logger.info(f"Using Azure OpenAI client: {cfg.api_base}")
            credential = DefaultAzureCredential(
                managed_identity_client_id=cfg.azure_managed_identity_client_id
            )
            token_provider = get_bearer_token_provider(
                credential, "https://cognitiveservices.azure.com/.default"
            )
            _openai_client = openai.AzureOpenAI(
                azure_endpoint=cfg.api_base,
                azure_ad_token_provider=token_provider,
                api_version=cfg.azure_api_version,
                timeout=timeout,
                max_retries=MAX_RETRIES,
            )
        elif is_gemini:
            logger.info(f"Using Gemini client: {cfg.api_base}")
            http_client = httpx.Client(
                limits=httpx.Limits(max_connections=pool_size),
                timeout=timeout,
            )
            _openai_client = OpenAI(
                base_url=cfg.api_base,
                api_key=cfg.GEMINI_API_KEY,
                http_client=http_client,
            )
        else:
            logger.info(f"Using standard OpenAI client: {cfg.api_base}")
            http_client = httpx.Client(
                limits=httpx.Limits(max_connections=pool_size),
                timeout=timeout,
            )
            _openai_client = OpenAI(
                base_url=cfg.api_base,
                api_key=cfg.api_key,
                http_client=http_client,
            )
    return _openai_client


def _remove_thinking_tags(content: str) -> str:
    """Remove internal thinking tags and their content from LLM responses

    Note: Does not remove <reasoning> tags because the prompt template requires LLM to output <reasoning> blocks,
    and Lean code may also contain similar strings. Only removes model internal reasoning tags.
    """
    if not content:
        return content
    patterns = [
        r'<think>.*?</think>',
        r'<thinking>.*?</thinking>',
    ]
    for pattern in patterns:
        content = re.sub(pattern, '', content, flags=re.DOTALL | re.IGNORECASE)
    return content


def llm_response(prompt: str) -> tuple[str, str, str]:
    """Single LLM call
    
    Returns:
        (code, raw_content, thinking) - extracted code, raw response content, thinking content
        
    Raises:
        RuntimeError: LLM call failed or returned empty response
    """
    cfg = get_config()
    
    try:
        client = get_openai_client()
        
        # Azure OpenAI uses max_completion_tokens, and some models do not support the temperature parameter
        if _is_azure_client:
            api_params = {
                "model": cfg.model,
                "max_completion_tokens": cfg.max_tokens,
                "messages": [{"role": "user", "content": prompt}],
            }
            # Add reasoning_effort (only effective for reasoning models)
            if hasattr(cfg, 'reasoning_effort') and cfg.reasoning_effort:
                api_params["reasoning_effort"] = cfg.reasoning_effort
            response = client.chat.completions.create(**api_params)
        else:
            response = client.chat.completions.create(
                model=cfg.model,
                temperature=cfg.temperature,
                max_tokens=cfg.max_tokens,
                messages=[{"role": "user", "content": prompt}],
            )
        
        if not response.choices:
            raise RuntimeError("LLM returned empty response: response.choices is empty")
        
        message = response.choices[0].message
        raw_content = message.content or ""
        # Consistent with prover: some reasoning models place body in model_extra.reasoning/content, with content as None
        if not raw_content and getattr(message, "model_extra", None) and isinstance(message.model_extra, dict):
            raw_content = message.model_extra.get("reasoning") or message.model_extra.get("content") or ""

        # Try to get reasoning_content (Azure OpenAI o1/o3/gpt-5 and other reasoning models)
        # If this field is not available, try to extract thinking tag content from content
        thinking = getattr(message, 'reasoning_content', "")

        # Clean thinking tags from content
        clean_content = _remove_thinking_tags(raw_content)
        code = extract_lean4_code(clean_content, warn_on_empty=False)
        
        if hasattr(response, 'usage') and response.usage:
            update_usage(response.usage)
        check_budget()
        
        return code, raw_content, thinking or ""
        
    except BudgetExceededError:
        raise
    except openai.RateLimitError as e:
        raise RuntimeError(f"LLM API rate limit: {e}") from e
    except openai.APIConnectionError as e:
        raise RuntimeError(f"LLM API connection failed: {e}") from e
    except openai.APIStatusError as e:
        raise RuntimeError(f"LLM API error (status={e.status_code}): {e.message}") from e
    except httpx.TimeoutException as e:
        raise RuntimeError(f"LLM API request timeout: {e}") from e
    except Exception as e:
        raise RuntimeError(f"LLM call failed: {type(e).__name__}: {e}") from e
