#!/usr/bin/env python3
"""
Test the LLM API used by the Prove stage (matching config.yaml prove.llm).

Usage (from project root):
  python scripts/test_llm_api.py
  python scripts/test_llm_api.py -c config.yaml
"""
import argparse
import asyncio
import sys
from pathlib import Path

# Ensure prover can be imported
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import openai


def load_prove_llm_config(config_path: str):
    import yaml
    with open(config_path, "r", encoding="utf-8") as f:
        data = yaml.safe_load(f)
    prove = data.get("prove", {})
    llm = prove.get("llm", {})
    return {
        "api_base": llm.get("api_base", ""),
        "api_key": llm.get("api_key", "dummy"),
        "model": llm.get("model", ""),
        "temperature": llm.get("temperature", 0.7),
        "max_tokens": llm.get("max_tokens", 8192),
        "timeout": llm.get("timeout", 300),
    }


async def test_api(config_path: str = "config.yaml"):
    cfg = load_prove_llm_config(config_path)
    print("Config:", cfg)
    print()

    client = openai.AsyncOpenAI(
        api_key=cfg["api_key"],
        base_url=cfg["api_base"] if cfg["api_base"] else None,
        timeout=cfg["timeout"],
    )

    try:
        response = await client.chat.completions.create(
            model=cfg["model"],
            messages=[
                {"role": "user", "content": "Say exactly: API test OK"},
            ],
            temperature=0,
            max_tokens=64,
        )
    except Exception as e:
        print("Request exception:", type(e).__name__, e)
        return

    print("HTTP request successful")
    print("Number of response.choices:", len(response.choices))
    if not response.choices:
        print("response.choices is empty -> no content, equivalent to None")
        return

    choice = response.choices[0]
    msg = choice.message
    content = msg.content

    # Reasoning models may put the body in model_extra.reasoning
    if getattr(msg, "model_extra", None) and isinstance(msg.model_extra, dict):
        print("choice.message.model_extra keys:", list(msg.model_extra.keys()))
        for k, v in msg.model_extra.items():
            if v is not None and isinstance(v, str):
                print(f"  model_extra[{k}] first 120 chars:", repr(v[:120]))
    print()

    print("choice.message.content type:", type(content))
    print("choice.message.content is None:", content is None)
    if content is None:
        print("-> This is why LLM Response: None appears in run: the API returns message.content as None")
    else:
        print("content first 200 chars:", repr(content[:200]) if len(content) > 200 else repr(content))
    if hasattr(response, "usage") and response.usage:
        print("usage:", response.usage)


def main():
    p = argparse.ArgumentParser(description="Test Prove LLM API")
    p.add_argument("-c", "--config", default="config.yaml", help="Config file path")
    args = p.parse_args()
    config_path = Path(__file__).resolve().parent.parent / args.config
    if not config_path.exists():
        print("Config file not found:", config_path)
        sys.exit(1)
    asyncio.run(test_api(str(config_path)))


if __name__ == "__main__":
    main()
