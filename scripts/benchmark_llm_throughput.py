#!/usr/bin/env python3
"""
Measure LLM service throughput: QPS, latency percentiles, tokens/s (if API returns usage).

Usage (from project root):
  # Specify URL and model name
  python scripts/benchmark_llm_throughput.py --url http://localhost:8901/v1 --model your-model-name

  # Optional: request count, concurrency, per-request max_tokens
  python scripts/benchmark_llm_throughput.py --url http://localhost:8901/v1 --model your-model -n 20 -c 4 --max-tokens 256
"""
import argparse
import asyncio
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import openai


def _ensure_v1(url: str) -> str:
    url = url.rstrip("/")
    if not url.endswith("/v1"):
        url = f"{url}/v1"
    return url


async def _one_request(
    client: openai.AsyncOpenAI,
    model: str,
    max_tokens: int,
    prompt: str = "Reply with one short sentence: hello.",
) -> tuple[float, int, int, bool]:
    """Send one request, return (elapsed_seconds, input_tokens, output_tokens, success)."""
    start = time.perf_counter()
    inp, out = 0, 0
    try:
        resp = await client.chat.completions.create(
            model=model,
            messages=[{"role": "user", "content": prompt}],
            temperature=0,
            max_tokens=max_tokens,
        )
        elapsed = time.perf_counter() - start
        if getattr(resp, "usage", None):
            inp = getattr(resp.usage, "prompt_tokens", 0) or 0
            out = getattr(resp.usage, "completion_tokens", 0) or 0
        return (elapsed, inp, out, True)
    except Exception:
        elapsed = time.perf_counter() - start
        return (elapsed, 0, 0, False)


def _percentile(sorted_values: list[float], p: float) -> float:
    if not sorted_values:
        return 0.0
    k = (len(sorted_values) - 1) * p / 100
    f = int(k)
    c = f + 1 if f + 1 < len(sorted_values) else f
    return sorted_values[f] + (k - f) * (sorted_values[c] - sorted_values[f])


async def run_benchmark(
    url: str,
    model: str,
    num_requests: int = 20,
    concurrency: int = 4,
    max_tokens: int = 256,
    api_key: str = "dummy",
    timeout: int = 120,
) -> None:
    base_url = _ensure_v1(url)
    client = openai.AsyncOpenAI(
        api_key=api_key,
        base_url=base_url,
        timeout=timeout,
    )

    print(f"Target: {base_url}")
    print(f"Model: {model}")
    print(f"Requests: {num_requests}, Concurrency: {concurrency}, max_tokens: {max_tokens}")
    print()

    sem = asyncio.Semaphore(concurrency)

    async def limited_request():
        async with sem:
            return await _one_request(client, model, max_tokens)

    wall_start = time.perf_counter()
    tasks = [limited_request() for _ in range(num_requests)]
    results = await asyncio.gather(*tasks)
    wall_elapsed = time.perf_counter() - wall_start

    latencies = [r[0] for r in results]
    input_tokens = sum(r[1] for r in results)
    output_tokens = sum(r[2] for r in results)
    ok = sum(1 for r in results if r[3])
    failed = num_requests - ok

    latencies_sorted = sorted(latencies)
    total_tokens = input_tokens + output_tokens

    print("========== Throughput Results ==========")
    print(f"Success: {ok}/{num_requests}, Failed: {failed}")
    print(f"Total wall-clock time: {wall_elapsed:.2f} s")
    print(f"QPS (requests/sec): {ok / wall_elapsed:.2f}")
    if total_tokens > 0:
        print(f"Total tokens (input + output): {total_tokens}, tokens/s: {total_tokens / wall_elapsed:.1f}")
    print()
    print("Latency (seconds):")
    print(f"  min: {min(latencies_sorted):.2f}, max: {max(latencies_sorted):.2f}, avg: {sum(latencies_sorted)/len(latencies_sorted):.2f}")
    print(f"  p50: {_percentile(latencies_sorted, 50):.2f}, p95: {_percentile(latencies_sorted, 95):.2f}, p99: {_percentile(latencies_sorted, 99):.2f}")


def main():
    p = argparse.ArgumentParser(description="Benchmark LLM API throughput")
    p.add_argument("--url", required=True, help="LLM service URL, e.g. http://localhost:8901/v1")
    p.add_argument("--model", required=True, help="Model name (or last segment of path)")
    p.add_argument("-n", "--num-requests", type=int, default=20, help="Total number of requests")
    p.add_argument("-c", "--concurrency", type=int, default=4, help="Concurrency level")
    p.add_argument("--max-tokens", type=int, default=256, help="max_tokens per request")
    p.add_argument("--api-key", default="dummy", help="API Key")
    p.add_argument("--timeout", type=int, default=120, help="Per-request timeout (seconds)")
    args = p.parse_args()

    asyncio.run(
        run_benchmark(
            url=args.url,
            model=args.model,
            num_requests=args.num_requests,
            concurrency=args.concurrency,
            max_tokens=args.max_tokens,
            api_key=args.api_key,
            timeout=args.timeout,
        )
    )


if __name__ == "__main__":
    main()
