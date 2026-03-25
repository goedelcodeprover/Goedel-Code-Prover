#!/usr/bin/env python3
"""
Lean Verifier Server test script.
Exercises basic server functionality.
"""

import json
import time
import requests
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from loguru import logger


def test_health_endpoint(base_url: str = "http://localhost:8000"):
    """Test the health check endpoint."""
    logger.info("Testing health check endpoint...")
    
    try:
        response = requests.get(f"{base_url}/health/init", timeout=10)
        response.raise_for_status()
        
        data = response.json()
        logger.info(f"Health check OK: {data}")
        
        return data.get("status") == "healthy"
        
    except Exception as e:
        logger.error(f"Health check failed: {e}")
        return False


def test_single_verify(base_url: str = "http://localhost:8000"):
    """Test the single-verify endpoint."""
    logger.info("Testing single-verify endpoint...")
    
    test_code = "def hello : String := \"Hello, Lean!\""
    
    payload = {
        "code": test_code,
        "timeout": 30,
        "max_retries": 2
    }
    
    try:
        response = requests.post(f"{base_url}/verify", json=payload, timeout=60)
        response.raise_for_status()
        
        data = response.json()
        is_valid = data.get("is_valid_no_sorry", False)
        logger.info(f"Single verify: is_valid={is_valid}")
        
        # If verification failed, print details
        if not is_valid:
            logger.warning(f"\n  ========== Single verify failed ==========")
            logger.warning(f"  Test code:\n{test_code}")
            logger.warning(f"  is_valid_no_sorry: {data.get('is_valid_no_sorry', False)}")
            logger.warning(f"  is_valid_with_sorry: {data.get('is_valid_with_sorry', False)}")
            logger.warning(f"  Error message: {data.get('error_message', 'N/A')}")
            logger.warning(f"  Full response: {data.get('response', {})}")
            logger.warning(f"  =====================================\n")
        
        return is_valid
        
    except Exception as e:
        logger.error(f"Single verify failed: {e}")
        return False


def test_batch_verify(base_url: str = "http://localhost:8000"):
    """Test the batch-verify endpoint."""
    
    # Optional: clear cache before test for clean stats
    # logger.info("🗑️  Clearing cache...")
    # try:
    #     requests.post(f"{base_url}/cache/clear", timeout=5)
    #     logger.info("✅ Cache cleared")
    # except Exception as e:
    #     logger.warning(f"⚠️ Failed to clear cache: {e}")
    
    test_codes = [
        "import Mathlib\n\ndef add (a b : Nat) : Nat := a + b",
        "import Mathlib\n\ndef mul (a b : Nat) : Nat := a * b",
        "import Mathlib\n\ndef sub (a b : Nat) : Nat := if a >= b then a - b else 0"
    ] * 10

    logger.info(f"Testing batch-verify endpoint, test cases: {len(test_codes)}")
    
    payload = {
        "codes": test_codes,
        "timeout": 30,
        "max_retries": 2
    }
    
    try:
        start_time = time.time()
        response = requests.post(f"{base_url}/verify/batch", json=payload, timeout=600)
        response.raise_for_status()
        elapsed = time.time() - start_time
        
        data = response.json()
        logger.info(f"Batch verify succeeded")
        
        results = data.get("results", [])
        if not results:
            logger.error("No results returned")
            return False
        
        # Resource usage report
        processing_time = data.get("processing_time", elapsed)
        throughput = data.get("throughput", len(test_codes) / elapsed if elapsed > 0 else 0)
        cpu_stats = data.get("cpu_stats", {})
        cache_stats = data.get("cache_stats", {})
        config = data.get("config", {})
        
        logger.info("📊 Batch verify resource usage:")
        logger.info(f"  - Processing time: {processing_time:.2f}s")
        logger.info(f"  - Throughput: {throughput:.1f} codes/s")
        if cpu_stats:
            logger.info(f"  - Avg CPU: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
            logger.info(f"  - Max CPU: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
        if cache_stats and cache_stats.get('enabled'):
            logger.info(f"  - Cache hit rate: {cache_stats.get('hit_rate', 'N/A')}")
            logger.info(f"  - Cache hits: {cache_stats.get('total_hits', 0)}")
            logger.info(f"  - Cache misses: {cache_stats.get('total_misses', 0)}")
        logger.info(f"  - Batch size: {config.get('batch_size', 'N/A')}")
        logger.info(f"  - Concurrency: {config.get('concurrency', 'N/A')}")
        
        # Failed tasks
        failed_results = [r for r in results if not r.get("is_valid_no_sorry", False)]
        if failed_results:
            logger.warning(f"⚠️  {len(failed_results)} verification(s) failed:")
            for i, r in enumerate(failed_results[:5]):  # show first 5
                error_msg = r.get("error_message", "Unknown error")
                code_full = r.get("problem", "")
                response = r.get("response", {})
                
                logger.warning(f"\n  ========== Failure [{i+1}] ==========")
                logger.warning(f"  Full code:\n{code_full}")
                logger.warning(f"  Error: {error_msg}")
                logger.warning(f"  is_valid_no_sorry: {r.get('is_valid_no_sorry', False)}")
                logger.warning(f"  is_valid_with_sorry: {r.get('is_valid_with_sorry', False)}")
                if response:
                    logger.warning(f"  Response: {response}")
                logger.warning(f"  =====================================\n")
        
        all_valid = all(result.get("is_valid_no_sorry", False) for result in results)
        logger.info(f"  - Passed: {sum(1 for r in results if r.get('is_valid_no_sorry'))}/{len(results)}")
        
        return all_valid and len(results) == len(test_codes)
        
    except Exception as e:
        logger.error(f"Batch verify failed: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return False
    
def test_batch_verify_with_cache(base_url: str = "http://localhost:8000"):
    """Test batch-verify with cache behavior."""
    
    # Clear cache before test for clean stats
    logger.info("🗑️  Clearing cache...")
    try:
        requests.post(f"{base_url}/cache/clear", timeout=5)
        logger.info("✅ Cache cleared")
    except Exception as e:
        logger.warning(f"⚠️ Failed to clear cache: {e}")
    
    # Workload design:
    # Need task count >> worker count so the same worker handles multiple tasks and reuses cache.
    # Example: ~30 workers, 150 tasks → ~5 tasks per worker on average.
    # - 100 with Mathlib (should share one cached env)
    # - 50 with Aesop (should share another)
    test_codes = [
        "import Mathlib\n\ndef add (a b : Nat) : Nat := a + b",
        "import Mathlib\n\ndef mul (a b : Nat) : Nat := a * b",
        "import Aesop\n\ndef sub (a b : Nat) : Nat := if a >= b then a - b else 0"
    ] * 50  # 150 test cases
    
    logger.info(f"Testing batch-verify (with cache), test cases: {len(test_codes)}")
    logger.info(f"  - Expect: 100 Mathlib imports (cache hits expected)")
    logger.info(f"  - Expect: 50 Aesop imports (cache hits expected)")
    logger.info(f"  - Intent: many tasks per worker to exercise cache reuse")
    
    payload = {
        "codes": test_codes,
        "timeout": 30,
        "max_retries": 2
    }
    
    try:
        start_time = time.time()
        response = requests.post(f"{base_url}/verify/batch", json=payload, timeout=600)
        response.raise_for_status()
        elapsed = time.time() - start_time
        
        data = response.json()
        logger.info(f"Batch verify succeeded")
        
        results = data.get("results", [])
        if not results:
            logger.error("No results returned")
            return False
        
        # Resource usage report
        processing_time = data.get("processing_time", elapsed)
        throughput = data.get("throughput", len(test_codes) / elapsed if elapsed > 0 else 0)
        cpu_stats = data.get("cpu_stats", {})
        cache_stats = data.get("cache_stats", {})
        config = data.get("config", {})
        
        logger.info("📊 Batch verify resource usage:")
        logger.info(f"  - Processing time: {processing_time:.2f}s")
        logger.info(f"  - Throughput: {throughput:.1f} codes/s")
        if cpu_stats:
            logger.info(f"  - Avg CPU: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
            logger.info(f"  - Max CPU: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
        
        # Cache effectiveness
        if cache_stats and cache_stats.get('enabled'):
            total_hits = cache_stats.get('total_hits', 0)
            total_misses = cache_stats.get('total_misses', 0)
            hit_rate_str = cache_stats.get('hit_rate', '0.0%')
            
            logger.info(f"🎯 Cache stats:")
            logger.info(f"  - Hits: {total_hits}")
            logger.info(f"  - Misses: {total_misses}")
            logger.info(f"  - Hit rate: {hit_rate_str}")
            
            # Verify cache is working
            if total_hits + total_misses > 0:
                hit_rate = total_hits / (total_hits + total_misses) * 100
                if hit_rate > 0:
                    logger.info(f"  ✅ Cache active — hit rate {hit_rate:.1f}%")
                else:
                    logger.warning(f"  ⚠️  No cache hits — check configuration")
            else:
                logger.warning(f"  ⚠️  No cache statistics")
        else:
            logger.warning("  ⚠️  Cache disabled or stats unavailable")
        
        logger.info(f"  - Batch size: {config.get('batch_size', 'N/A')}")
        logger.info(f"  - Concurrency: {config.get('concurrency', 'N/A')}")
        
        # Failed tasks
        failed_results = [r for r in results if not r.get("is_valid_no_sorry", False)]
        if failed_results:
            logger.warning(f"⚠️  {len(failed_results)} verification(s) failed:")
            for i, r in enumerate(failed_results[:5]):  # show first 5
                error_msg = r.get("error_message", "Unknown error")
                code_full = r.get("problem", "")
                response = r.get("response", {})
                
                logger.warning(f"\n  ========== Failure [{i+1}] ==========")
                logger.warning(f"  Full code:\n{code_full}")
                logger.warning(f"  Error: {error_msg}")
                logger.warning(f"  is_valid_no_sorry: {r.get('is_valid_no_sorry', False)}")
                logger.warning(f"  is_valid_with_sorry: {r.get('is_valid_with_sorry', False)}")
                if response:
                    logger.warning(f"  Response detail: {response}")
                logger.warning(f"  =====================================\n")
        
        # Verification summary
        valid_count = sum(1 for r in results if r.get('is_valid_no_sorry'))
        logger.info(f"  - Passed: {valid_count}/{len(results)}")
        
        all_valid = all(result.get("is_valid_no_sorry", False) for result in results)
        correct_count = len(results) == len(test_codes)
        
        return all_valid and correct_count
        
    except Exception as e:
        logger.error(f"Batch verify failed: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return False
    
    
    
def test_concurrent_verify(base_url: str = "http://localhost:8000"):
    """Test concurrent batch verification."""
    
    # Optional: clear cache before test
    # logger.info("🗑️  Clearing cache...")
    # try:
    #     requests.post(f"{base_url}/cache/clear", timeout=5)
    #     logger.info("✅ Cache cleared")
    # except Exception as e:
    #     logger.warning(f"⚠️ Failed to clear cache: {e}")
    
    test_batches = [
        ["def add (a b : Nat) : Nat := a + b"] * 50,
        ["def mul (a b : Nat) : Nat := a * b"] * 50,
        ["def sub (a b : Nat) : Nat := if a >= b then a - b else 0"] * 50,
        ["def square (x : Nat) : Nat := x * x"] * 50,
        ["def isZero (n : Nat) : Bool := n == 0"] * 50
    ]

    num_concurrent = len(test_batches)
    total_codes = sum(len(batch) for batch in test_batches)
    logger.info(f"Testing {num_concurrent} concurrent batches")
    logger.info(f"Cases per batch: {len(test_batches[0])}")
    logger.info(f"Total test cases: {total_codes}")
    logger.info(f"Concurrent requests: {num_concurrent}")
    
    def send_batch_request(batch_id: int, codes: list):
        payload = {"codes": codes, "timeout": 30, "max_retries": 2}
        start = time.time()
        try:
            response = requests.post(f"{base_url}/verify/batch", json=payload, timeout=600)
            response.raise_for_status()
            elapsed = time.time() - start
            data = response.json()
            
            results = data.get("results", [])
            success = len(results) == len(codes) and all(result.get("is_valid_no_sorry", False) for result in results)
            
            # Collect resource usage
            processing_time = data.get("processing_time", elapsed)
            throughput = data.get("throughput", len(codes) / elapsed if elapsed > 0 else 0)
            cpu_stats = data.get("cpu_stats", {})
            cache_stats = data.get("cache_stats", {})
            config = data.get("config", {})
            
            return {
                "batch_id": batch_id,
                "success": success,
                "elapsed": elapsed,
                "processing_time": processing_time,
                "throughput": throughput,
                "cpu_stats": cpu_stats,
                "cache_stats": cache_stats,
                "config": config,
                "total_codes": len(codes)
            }
        except Exception as e:
            logger.error(f"Batch request {batch_id} failed: {e}")
            return {
                "batch_id": batch_id,
                "success": False,
                "elapsed": time.time() - start,
                "processing_time": time.time() - start,
                "throughput": 0,
                "cpu_stats": {},
                "cache_stats": {},
                "config": {},
                "error": str(e)
            }
    
    try:
        start_time = time.time()
        
        with ThreadPoolExecutor(max_workers=num_concurrent) as executor:
            futures = {
                executor.submit(send_batch_request, i, test_batches[i]): i
                for i in range(num_concurrent)
            }
            
            results = []
            for future in as_completed(futures):
                result = future.result()
                results.append(result)
                logger.info(f"Batch {result['batch_id']} done: success={result['success']}, time={result['elapsed']:.2f}s")
        
        total_time = time.time() - start_time
        success_count = sum(1 for r in results if r.get("success"))
        avg_time = sum(r["elapsed"] for r in results) / len(results)
        
        # Aggregate resource usage
        successful_results = [r for r in results if r.get("success")]
        if successful_results:
            avg_throughput = sum(r["throughput"] for r in successful_results) / len(successful_results)
            avg_cpu = sum(r["cpu_stats"].get("avg_cpu_percent", 0) for r in successful_results) / len(successful_results) if successful_results else 0
            max_cpu = max(r["cpu_stats"].get("max_cpu_percent", 0) for r in successful_results) if successful_results else 0
            
            # Total cases processed
            total_processed = sum(r["total_codes"] for r in successful_results)
            
            # Cache aggregates
            total_cache_hits = sum(r["cache_stats"].get("total_hits", 0) for r in successful_results if r.get("cache_stats", {}).get("enabled"))
            total_cache_misses = sum(r["cache_stats"].get("total_misses", 0) for r in successful_results if r.get("cache_stats", {}).get("enabled"))
            
            logger.info(f"📊 Concurrent test resource usage:")
            logger.info(f"  - Wall time: {total_time:.2f}s")
            logger.info(f"  - Successful requests: {success_count}/{num_concurrent}")
            logger.info(f"  - Cases processed: {total_processed}")
            logger.info(f"  - Avg request time: {avg_time:.2f}s")
            logger.info(f"  - Parallel speedup: {(avg_time * num_concurrent) / total_time:.2f}x")
            logger.info(f"  - Avg throughput: {avg_throughput:.1f} codes/s")
            logger.info(f"  - Avg CPU: {avg_cpu:.1f}%")
            logger.info(f"  - Max CPU: {max_cpu:.1f}%")
            if total_cache_hits + total_cache_misses > 0:
                cache_hit_rate = total_cache_hits / (total_cache_hits + total_cache_misses) * 100
                logger.info(f"  - Cache hit rate: {cache_hit_rate:.1f}%")
                logger.info(f"  - Cache hits: {total_cache_hits}, misses: {total_cache_misses}")
            
            # Per-batch config
            logger.info(f"📋 Batch details:")
            for result in successful_results:
                config = result["config"]
                batch_idx = result['batch_id']
                logger.info(f"  - Batch {batch_idx}: "
                          f"{result['total_codes']} cases, "
                          f"batch_size={config.get('batch_size', 'N/A')}, "
                          f"concurrency={config.get('concurrency', 'N/A')}")
        else:
            logger.error("❌ No successful requests — cannot compute resource usage")
        
        success_rate = success_count / num_concurrent
        parallel_efficiency = (avg_time * num_concurrent) / total_time
        
        return success_rate >= 0.75 and parallel_efficiency >= 1.5
        
    except Exception as e:
        logger.error(f"Concurrent batch test failed: {e}")
        return False


def test_error_handling(base_url: str = "http://localhost:8000"):
    """Test error handling."""
    logger.info("Testing error handling...")
    
    invalid_code = "invalid lean code syntax @#$%"
    
    payload = {"code": invalid_code, "timeout": 10, "max_retries": 1}
    
    try:
        response = requests.post(f"{base_url}/verify", json=payload, timeout=30)
        response.raise_for_status()
        
        data = response.json()
        is_valid = data.get("is_valid_no_sorry", True)
        error_msg = data.get("error_message")
        
        # Invalid code or an error message means handling behaved as expected
        result = not is_valid or (error_msg is not None)
        logger.info(f"Error handling test: is_valid={is_valid}, has_error={error_msg is not None}")
        
        return result
        
    except Exception as e:
        logger.error(f"Error handling test failed: {e}")
        return False


def test_cache_stats(base_url: str = "http://localhost:8000"):
    """Test the cache stats endpoint."""
    logger.info("Testing cache stats endpoint...")
    
    try:
        response = requests.get(f"{base_url}/cache/stats", timeout=10)
        response.raise_for_status()
        
        data = response.json()
        logger.info("Cache stats retrieved OK")
        
        has_workers = "workers" in data
        has_aggregate = "aggregate" in data
        
        if not (has_workers and has_aggregate):
            logger.error(f"Response missing required fields: {data.keys()}")
            return False
        
        # Show cache stats
        aggregate = data.get("aggregate", {})
        logger.info("📊 Cache stats:")
        logger.info(f"  - Total hits: {aggregate.get('total_hits', 0)}")
        logger.info(f"  - Total misses: {aggregate.get('total_misses', 0)}")
        logger.info(f"  - Hit rate: {aggregate.get('hit_rate', 'N/A')}")
        logger.info(f"  - Workers: {len(data.get('workers', []))}")
        
        return True
        
    except Exception as e:
        logger.error(f"Cache stats test failed: {e}")
        return False


def test_ray_stats(base_url: str = "http://localhost:8000"):
    """Test the Ray cluster stats endpoint."""
    logger.info("Testing Ray cluster stats endpoint...")
    
    try:
        response = requests.get(f"{base_url}/health/stats", timeout=10)
        response.raise_for_status()
        
        data = response.json()
        logger.info("Ray stats retrieved OK")
        
        has_cluster = "cluster" in data
        has_usage = "usage" in data
        has_workers = "workers" in data
        has_nodes = "nodes" in data
        
        if not (has_cluster and has_usage and has_workers and has_nodes):
            logger.error(f"Response missing required fields: {data.keys()}")
            return False
        
        # Cluster resources
        logger.info("📊 Cluster resources:")
        if "CPU" in data["cluster"]:
            cpu = data["cluster"]["CPU"]
            logger.info(f"  - CPU: {cpu['used']:.1f}/{cpu['total']:.1f} cores ({cpu['utilization_percent']:.1f}%)")
        
        if "memory" in data["cluster"]:
            mem = data["cluster"]["memory"]
            mem_gb_total = mem['total'] / (1024**3)
            mem_gb_used = mem['used'] / (1024**3)
            logger.info(f"  - Memory: {mem_gb_used:.1f}/{mem_gb_total:.1f} GB ({mem['utilization_percent']:.1f}%)")
        
        logger.info(f"  - Workers: {data.get('workers', {}).get('total', 0)}")
        logger.info(f"  - Cluster nodes: {len(data.get('nodes', []))}")
        
        return True
        
    except Exception as e:
        logger.error(f"Ray stats test failed: {e}")
        return False


def test_stress_with_testset(
    base_url: str = "http://localhost:8000",
    test_file: str = "test/test_set.json",
):
    """
    Stress test: run all problems from test_set.json in one batch request.

    Args:
        base_url: Server base URL.
        test_file: Path to test data JSON.
    """
    logger.info("=" * 80)
    logger.info("🔥 Stress test: full test_set.json run")
    logger.info("=" * 80)
    
    # Load test data
    test_path = Path(test_file)
    if not test_path.exists():
        logger.error(f"Test file not found: {test_file}")
        return False
    
    try:
        with open(test_path, 'r') as f:
            test_data = json.load(f)
                    
        test_data = test_data[:1000]
        total_cases = len(test_data)
        logger.info(f"📂 Loaded {total_cases} test cases")
        
        # Extract code snippets
        codes = [item['code'] for item in test_data]
        num_codes = len(codes)
        
        logger.info(f"🎯 Test setup:")
        logger.info(f"  - Total cases: {num_codes}")
        
        # Optional: clear cache for clean stats
        # logger.info("🗑️  Clearing cache...")
        # try:
        #     requests.post(f"{base_url}/cache/clear", timeout=60)
        #     logger.info("✅ Cache cleared")
        # except Exception as e:
        #     logger.warning(f"⚠️ Failed to clear cache: {e}")
        
        # Send batch request
        logger.info("🚀 Starting stress test...")
        start_time = time.time()
        
        payload = {
            "codes": codes,
            "timeout": 60,
            "max_retries": 2,
            "max_tasks_per_worker": 10
        }
        
        try:
            response = requests.post(
                f"{base_url}/verify/batch",
                json=payload,
                timeout=3600  # 1 hour
            )
            response.raise_for_status()
            elapsed = time.time() - start_time
            
            data = response.json()
            results = data.get("results", [])
            
            if not results:
                logger.error("❌ No results returned")
                return False
            
            # Tally results
            valid_no_sorry = sum(1 for r in results if r.get("is_valid_no_sorry", False))
            valid_with_sorry = sum(1 for r in results if r.get("is_valid_with_sorry", False))
            success = valid_no_sorry 
            failed = len(results) - valid_no_sorry
            
            # Performance metrics
            processing_time = data.get("processing_time", elapsed)
            throughput = data.get("throughput", num_codes / elapsed if elapsed > 0 else 0)
            cpu_stats = data.get("cpu_stats", {})
            cache_stats = data.get("cache_stats", {})
            config = data.get("config", {})
            
            # Detailed stats
            logger.info("=" * 80)
            logger.info("📊 Stress test results")
            logger.info("=" * 80)
            
            logger.info("🎯 Verification:")
            logger.info(f"  - Total cases: {len(results)}")
            logger.info(f"  - ✅ Pass (no sorry): {valid_no_sorry} ({valid_no_sorry/len(results)*100:.1f}%)")
            logger.info(f"  - ⚠️  Pass (with sorry): {valid_with_sorry} ({valid_with_sorry/len(results)*100:.1f}%)")
            logger.info(f"  - ❌ Failed: {failed} ({failed/len(results)*100:.1f}%)")
            
            logger.info("")
            logger.info("⚡ Performance:")
            logger.info(f"  - Total time: {processing_time:.2f}s ({processing_time/60:.1f} min)")
            logger.info(f"  - Avg throughput: {throughput:.2f} codes/s")
            logger.info(f"  - Avg per case: {processing_time/len(results)*1000:.1f}ms")
            
            if cpu_stats:
                logger.info("")
                logger.info("💻 CPU:")
                logger.info(f"  - Avg CPU: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
                logger.info(f"  - Max CPU: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
                logger.info(f"  - Min CPU: {cpu_stats.get('min_cpu_percent', 0):.1f}%")
            
            if cache_stats and cache_stats.get('enabled'):
                logger.info("")
                logger.info("🎯 Cache:")
                total_hits = cache_stats.get('total_hits', 0)
                total_misses = cache_stats.get('total_misses', 0)
                hit_rate_str = cache_stats.get('hit_rate', '0.0%')
                logger.info(f"  - Hits: {total_hits}")
                logger.info(f"  - Misses: {total_misses}")
                logger.info(f"  - Hit rate: {hit_rate_str}")
                
                if total_hits + total_misses > 0:
                    # Rough speedup estimate: hit ~0.05s, miss ~3.5s
                    time_with_cache = total_hits * 0.05 + total_misses * 3.5
                    time_without_cache = (total_hits + total_misses) * 3.5
                    speedup = time_without_cache / time_with_cache if time_with_cache > 0 else 1.0
                    logger.info(f"  - Est. speedup vs no cache: {speedup:.1f}x")
            
            if config:
                logger.info("")
                logger.info("⚙️  Configuration:")
                logger.info(f"  - Workers: {config.get('num_workers', 'N/A')}")
                logger.info(f"  - Replicas: {config.get('num_replicas', 'N/A')}")
                logger.info(f"  - Cache enabled: {config.get('cache_enabled', False)}")
                logger.info(f"  - Max cached envs: {config.get('max_cached_envs', 'N/A')}")
                logger.info(f"  - Max tasks per worker: {config.get('max_tasks_per_worker', 'N/A')}")
            
            # Sample successes / failures
            if success > 0:
                logger.info("")
                logger.info("✅ Success samples (first 10):")
                success_results = [r for r in results if r.get("is_valid_no_sorry", False)]
                
                for i, r in enumerate(success_results[:10]):
                    problem_name = test_data[results.index(r)].get('name', 'unknown')
                    logger.info(f"  [{i+1}] {problem_name}: {r}")
            
            if failed > 0:
                logger.info("")
                logger.warning(f"⚠️  Failure samples (first 10):")
                failed_results = [r for r in results if not r.get("is_valid_no_sorry", False)]
                
                for i, r in enumerate(failed_results[:10]):
                    problem_name = test_data[results.index(r)].get('name', 'unknown')
                    error_msg = r.get("error_message", "Unknown error")
                    logger.warning(f"  [{i+1}] {problem_name}: {error_msg}")
            
            logger.info("=" * 80)
            
            # Pass if result count matches submitted count
            success = len(results) == num_codes
            
            if success:
                logger.info(f"✅ Stress test passed — results: {len(results)}, submitted: {num_codes}")
            else:
                logger.error(f"❌ Stress test failed — results: {len(results)}, submitted: {num_codes}")
            
            return success
            
        except requests.Timeout:
            logger.error(f"❌ Request timed out (> 1 hour)")
            return False
        except Exception as e:
            logger.error(f"❌ Stress test failed: {e}")
            import traceback
            logger.error(traceback.format_exc())
            return False
    
    except Exception as e:
        logger.error(f"❌ Failed to load test data: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return False


def main():
    """Run selected integration tests."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Lean Verifier Server integration tests")
    parser.add_argument("--url", default="http://localhost:8000", help="Server base URL")
    parser.add_argument("--test", default="all", 
                       choices=["all", "health", "single", "batch", "batch_cache", "concurrent", "error", "cache", "stats", "stress"], 
                       help="Which test to run")
    
    args = parser.parse_args()
    
    logger.info("=" * 60)
    logger.info("Lean Verifier Server tests starting")
    logger.info("=" * 60)
    
    base_url = args.url.rstrip('/')
    results = {}
    
    # Run tests
    if args.test in ["all", "health"]:
        results["Health check"] = test_health_endpoint(base_url)

    if args.test in ["all", "single"]:
        results["Single verify"] = test_single_verify(base_url)
    
    if args.test in ["all", "batch"]:
        results["Batch verify"] = test_batch_verify(base_url)
    
    if args.test in ["all", "batch_cache"]:
        results["Batch verify (cache)"] = test_batch_verify_with_cache(base_url)
    
    if args.test == "stress":
        results["Stress test"] = test_stress_with_testset(
            base_url=base_url,
            test_file="test/test_set.json"
        )
    
    # if args.test in ["all", "concurrent"]:
    
    #     results["Concurrent"] = test_concurrent_verify(base_url)
    
    # if args.test in ["all", "error"]:
    #     results["Error handling"] = test_error_handling(base_url)
    
    # if args.test in ["all", "cache"]:
    #     results["Cache stats"] = test_cache_stats(base_url)
    
    # if args.test in ["all", "stats"]:
    #     results["Ray stats"] = test_ray_stats(base_url)
    
    # Print summary
    logger.info("=" * 60)
    logger.info("Test summary")
    logger.info("=" * 60)
    
    for test_name, result in results.items():
        status = "✅ PASS" if result else "❌ FAIL"
        logger.info(f"{test_name:12}: {status}")
    
    total_tests = len(results)
    passed_tests = sum(results.values())
    
    logger.info(f"Passed: {passed_tests}/{total_tests}")
    
    if passed_tests == total_tests:
        logger.info("🎉 All tests passed!")
        return 0
    else:
        logger.error("❌ Some tests failed")
        return 1


if __name__ == "__main__":
    exit(main())
