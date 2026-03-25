"""
Lean Verifier Server — example client.
Demonstrates how to talk to the server.
"""

import asyncio
import json
import time
from typing import List, Dict, Any
import aiohttp
import requests
from loguru import logger


class LeanVerifierClient:
    """Async HTTP client for the Lean verifier server."""
    
    def __init__(self, base_url: str = "http://localhost:8000"):
        self.base_url = base_url.rstrip('/')
        self.session = None
    
    async def __aenter__(self):
        """Async context manager entry."""
        self.session = aiohttp.ClientSession()
        return self
    
    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit."""
        if self.session:
            await self.session.close()
    
    async def health_check(self) -> Dict[str, Any]:
        """Call the health endpoint."""
        async with self.session.get(f"{self.base_url}/health") as response:
            return await response.json()
    
    async def verify_single(self, code: str, timeout: int = 60, parse_result: bool = True) -> Dict[str, Any]:
        """Verify a single snippet."""
        payload = {
            "code": code,
            "timeout": timeout,
            "parse_result": parse_result
        }
        
        async with self.session.post(
            f"{self.base_url}/verify",
            json=payload
        ) as response:
            return await response.json()
    
    async def verify_batch(self, codes: List[str], timeout: int = 60, parse_result: bool = True, use_tqdm: bool = False) -> Dict[str, Any]:
        """Verify a batch of snippets."""
        payload = {
            "codes": codes,
            "timeout": timeout,
            "parse_result": parse_result,
            "use_tqdm": use_tqdm
        }
        
        async with self.session.post(
            f"{self.base_url}/verify/batch",
            json=payload
        ) as response:
            return await response.json()
    
    async def verify_async(self, code: str, timeout: int = 60, parse_result: bool = True) -> Dict[str, Any]:
        """Submit async verification (if supported by server)."""
        payload = {
            "code": code,
            "timeout": timeout,
            "parse_result": parse_result
        }
        
        async with self.session.post(
            f"{self.base_url}/verify/async",
            json=payload
        ) as response:
            return await response.json()


class LeanVerifierSyncClient:
    """Synchronous HTTP client for the Lean verifier server."""
    
    def __init__(self, base_url: str = "http://localhost:8000"):
        self.base_url = base_url.rstrip('/')
    
    def health_check(self) -> Dict[str, Any]:
        """Call the health endpoint."""
        response = requests.get(f"{self.base_url}/health")
        response.raise_for_status()
        return response.json()
    
    def verify_single(self, code: str, timeout: int = 60, parse_result: bool = True) -> Dict[str, Any]:
        """Verify a single snippet."""
        payload = {
            "code": code,
            "timeout": timeout,
            "parse_result": parse_result
        }
        
        response = requests.post(f"{self.base_url}/verify", json=payload)
        response.raise_for_status()
        return response.json()
    
    def verify_batch(self, codes: List[str], timeout: int = 60, parse_result: bool = True, use_tqdm: bool = False) -> Dict[str, Any]:
        """Verify a batch of snippets."""
        payload = {
            "codes": codes,
            "timeout": timeout,
            "parse_result": parse_result,
            "use_tqdm": use_tqdm
        }
        
        response = requests.post(f"{self.base_url}/verify/batch", json=payload)
        response.raise_for_status()
        return response.json()
    
    def verify_async(self, code: str, timeout: int = 60, parse_result: bool = True) -> Dict[str, Any]:
        """Submit async verification (if supported by server)."""
        payload = {
            "code": code,
            "timeout": timeout,
            "parse_result": parse_result
        }
        
        response = requests.post(f"{self.base_url}/verify/async", json=payload)
        response.raise_for_status()
        return response.json()


async def demo_async_client():
    """Demo: async client."""
    logger.info("Async client demo")
    
    async with LeanVerifierClient() as client:
        # Health
        health = await client.health_check()
        logger.info(f"Server status: {health}")
        
        # Single verify
        test_code = """
        def hello : String := "Hello, Lean!"
        #check hello = "Hello, Lean!"
        """
        
        logger.info("Starting single verification...")
        result = await client.verify_single(test_code)
        logger.info(f"Verification result: {result}")
        
        # Batch verify
        test_codes = [
            "def add (a b : Nat) : Nat := a + b",
            "def mul (a b : Nat) : Nat := a * b",
            "def sub (a b : Nat) : Nat := if a >= b then a - b else 0"
        ]
        
        logger.info("Starting batch verification...")
        batch_result = await client.verify_batch(test_codes)
        logger.info(f"Batch result: {batch_result}")


def demo_sync_client():
    """Demo: sync client."""
    logger.info("Sync client demo")
    
    client = LeanVerifierSyncClient()
    
    # Health
    health = client.health_check()
    logger.info(f"Server status: {health}")
    
    # Single verify
    test_code = """
    def hello : String := "Hello, Lean!"
    #check hello = "Hello, Lean!"
    """
    
    logger.info("Starting single verification...")
    result = client.verify_single(test_code)
    logger.info(f"Verification result: {result}")
    
    # Batch verify
    test_codes = [
        "def add (a b : Nat) : Nat := a + b",
        "def mul (a b : Nat) : Nat := a * b",
        "def sub (a b : Nat) : Nat := if a >= b then a - b else 0"
    ]
    
    logger.info("Starting batch verification...")
    batch_result = client.verify_batch(test_codes)
    logger.info(f"Batch result: {batch_result}")


def benchmark_client():
    """Simple throughput demo."""
    logger.info("Benchmark")
    
    client = LeanVerifierSyncClient()
    
    # Test snippets
    test_codes = [
        "def add (a b : Nat) : Nat := a + b",
        "def mul (a b : Nat) : Nat := a * b",
        "def sub (a b : Nat) : Nat := if a >= b then a - b else 0",
        "def div (a b : Nat) : Nat := if b > 0 then a / b else 0",
        "def mod (a b : Nat) : Nat := if b > 0 then a % b else a"
    ] * 10  # 50 cases
    
    # Single-verify timing
    logger.info("Single-verify benchmark...")
    start_time = time.time()
    
    for i, code in enumerate(test_codes[:10]):  # First 10
        result = client.verify_single(code)
        if i % 5 == 0:
            logger.info(f"Completed {i+1}/10 verifications")
    
    single_time = time.time() - start_time
    logger.info(f"Single-verify total time: {single_time:.2f}s")
    
    # Batch timing
    logger.info("Batch benchmark...")
    start_time = time.time()
    
    batch_result = client.verify_batch(test_codes)
    
    batch_time = time.time() - start_time
    logger.info(f"Batch total time: {batch_time:.2f}s")
    logger.info(f"Speedup vs singles: {single_time/batch_time:.2f}x")


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Lean Verifier Client Demo")
    parser.add_argument("--mode", default="sync", choices=["sync", "async", "benchmark"], help="Run mode")
    parser.add_argument("--url", default="http://localhost:8000", help="Server base URL")
    
    args = parser.parse_args()
    
    if args.mode == "sync":
        demo_sync_client()
    elif args.mode == "async":
        asyncio.run(demo_async_client())
    elif args.mode == "benchmark":
        benchmark_client()
