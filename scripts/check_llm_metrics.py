#!/usr/bin/env python3
"""
Check current load and throughput via vLLM /metrics (Prometheus) to determine if at full capacity.

vLLM serves /metrics on the same port as the API, e.g.:
  http://localhost:8901/metrics

Usage (on a machine with access to the server):
  python scripts/check_llm_metrics.py --url http://localhost:8901
"""
import argparse
import re
import sys
from pathlib import Path
from urllib.request import urlopen

def fetch_metrics(url: str, timeout: int = 10) -> str:
    base = url.rstrip("/").removesuffix("/v1")
    metrics_url = f"{base}/metrics"
    with urlopen(metrics_url, timeout=timeout) as r:
        return r.read().decode("utf-8", errors="replace")


def parse_prometheus(text: str) -> dict[str, float]:
    """Parse Prometheus text format; take value of unlabeled or first series."""
    out = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        # metric_name {labels} value  or  metric_name value
        m = re.match(r"^([a-zA-Z_:][a-zA-Z0-9_:]*)\s+(?:\{[^}]*\}\s+)?([0-9.eE+-]+)\s*$", line)
        if m:
            name, val = m.group(1), float(m.group(2))
            if name not in out:  # keep only the first when there are multiple series
                out[name] = val
    return out


def main():
    p = argparse.ArgumentParser(description="Check vLLM /metrics for load and throughput")
    p.add_argument("--url", required=True, help="LLM service URL, e.g. http://localhost:8901")
    p.add_argument("--timeout", type=int, default=10, help="/metrics request timeout (seconds)")
    args = p.parse_args()

    try:
        raw = fetch_metrics(args.url, args.timeout)
    except Exception as e:
        print(f"Failed to fetch /metrics: {e}", file=sys.stderr)
        sys.exit(1)

    metrics = parse_prometheus(raw)

    # Common vLLM metric names (may be prefixed with vllm: or vllm_)
    running = None
    waiting = None
    gen_tokens = None
    prompt_tokens = None
    for k, v in metrics.items():
        if "num_requests_running" in k or "requests_running" in k:
            running = v
        if "num_requests_waiting" in k or "requests_waiting" in k:
            waiting = v
        if "generation_tokens" in k and "total" in k.lower() or k.endswith("generation_tokens"):
            gen_tokens = v
        if "prompt_tokens" in k and "by_source" not in k:
            prompt_tokens = v

    base = args.url.rstrip("/").removesuffix("/v1")
    print(f"Metrics source: {base}/metrics")
    print()

    if running is not None:
        print(f"Currently running requests (running): {int(running)}")
    else:
        print("Currently running requests (running): (metric not found)")
    if waiting is not None:
        print(f"Currently queued requests (waiting):  {int(waiting)}")
    else:
        print("Currently queued requests (waiting):  (metric not found)")

    if prompt_tokens is not None:
        print(f"Cumulative prompt tokens:         {int(prompt_tokens)}")
    if gen_tokens is not None:
        print(f"Cumulative generation tokens:    {int(gen_tokens)}")

    # Full-load check: high running + waiting > 0 means requests are queued (at capacity)
    print()
    if running is not None and waiting is not None:
        if waiting > 0:
            print("Conclusion: Full load (requests are queued)")
        elif running >= 1:
            print("Conclusion: Under load, no queuing (not at capacity)")
        else:
            print("Conclusion: Idle (no running requests)")
    elif running is not None:
        if running >= 8:
            print("Conclusion: High load (many running, possibly near capacity)")
        elif running >= 1:
            print("Conclusion: Under load, need waiting metric to determine if at capacity")
        else:
            print("Conclusion: Idle")
    else:
        print("Conclusion: vLLM request count metrics not found; check if /metrics is enabled or if metric names changed")

    # Print some raw lines for debugging
    vllm_lines = [l for l in raw.splitlines() if "vllm" in l.lower() and not l.strip().startswith("#")]
    if vllm_lines:
        print()
        print("Selected vLLM metric lines (for reference):")
        for l in vllm_lines[:30]:
            print(" ", l[:120] + ("..." if len(l) > 120 else ""))


if __name__ == "__main__":
    main()
