"""
Token usage tracking and budget management (shared by decompose / prove phases).
"""

import logging
import threading
from typing import Any, Dict

logger = logging.getLogger(__name__)

_usage_stats = {
    "prompt_tokens": 0,
    "completion_tokens": 0,
    "total_tokens": 0,
    "request_count": 0,
}
_usage_lock = threading.Lock()


class BudgetExceededError(Exception):
    """Budget exceeded error."""
    pass


def update_usage(usage) -> None:
    """Extract and accumulate token usage from an LLM response.usage object."""
    if usage is None:
        return
    with _usage_lock:
        _usage_stats["prompt_tokens"] += getattr(usage, "prompt_tokens", 0) or 0
        _usage_stats["completion_tokens"] += getattr(usage, "completion_tokens", 0) or 0
        _usage_stats["total_tokens"] += getattr(usage, "total_tokens", 0) or 0
        _usage_stats["request_count"] += 1


def get_usage_stats(
    *,
    input_price_per_million: float = 0.0,
    output_price_per_million: float = 0.0,
    budget_limit: float = 0.0,
    model: str = "",
) -> Dict[str, Any]:
    """Get token usage statistics and estimated cost.

    Args:
        input_price_per_million:  Input token price (USD per million tokens).
        output_price_per_million: Output token price (USD per million tokens).
        budget_limit: Budget cap in USD.
        model: Current model name.
    """
    with _usage_lock:
        stats = _usage_stats.copy()

    input_price = input_price_per_million / 1_000_000
    output_price = output_price_per_million / 1_000_000

    estimated_cost = (
        stats["prompt_tokens"] * input_price
        + stats["completion_tokens"] * output_price
    )

    stats["estimated_cost_usd"] = round(estimated_cost, 6)
    stats["budget_limit"] = budget_limit
    stats["model"] = model
    return stats


def check_budget(
    *,
    input_price_per_million: float = 0.0,
    output_price_per_million: float = 0.0,
    budget_limit: float = 0.0,
) -> None:
    """Check whether budget is exceeded; raises BudgetExceededError if so."""
    stats = get_usage_stats(
        input_price_per_million=input_price_per_million,
        output_price_per_million=output_price_per_million,
        budget_limit=budget_limit,
    )
    if stats["budget_limit"] > 0 and stats["estimated_cost_usd"] >= stats["budget_limit"]:
        raise BudgetExceededError(
            f"Budget exceeded! Spent ${stats['estimated_cost_usd']:.4f}, "
            f"limit is ${stats['budget_limit']:.2f}"
        )


def reset_usage_stats() -> None:
    """Reset token usage statistics."""
    global _usage_stats
    with _usage_lock:
        _usage_stats = {
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "total_tokens": 0,
            "request_count": 0,
        }


def print_usage_stats(
    *,
    input_price_per_million: float = 0.0,
    output_price_per_million: float = 0.0,
    budget_limit: float = 0.0,
    model: str = "",
) -> None:
    """Print token usage statistics."""
    stats = get_usage_stats(
        input_price_per_million=input_price_per_million,
        output_price_per_million=output_price_per_million,
        budget_limit=budget_limit,
        model=model,
    )
    logger.info(
        f"Token usage stats: "
        f"requests={stats['request_count']}, "
        f"input={stats['prompt_tokens']:,}, "
        f"output={stats['completion_tokens']:,}, "
        f"total={stats['total_tokens']:,}, "
        f"estimated_cost=${stats['estimated_cost_usd']:.4f}"
    )
