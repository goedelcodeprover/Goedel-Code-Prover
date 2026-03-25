#!/usr/bin/env python3
"""
Measure how different max_env_reuse_count values affect performance.

Goal: find a good environment reuse limit.
- Too low: frequent env restarts, higher overhead.
- Too high: risk of memory leaks/fragmentation and slower performance.
"""

import requests
import time
import json
from pathlib import Path
from loguru import logger
import statistics

# Logging setup
logger.remove()
logger.add(
    lambda msg: print(msg, end=""),
    level="INFO",
    format="<green>{time:HH:mm:ss}</green> | <level>{level: <8}</level> | <level>{message}</level>"
)


def test_reuse_count_performance(
    base_url: str = "http://localhost:8000",
    num_tests: int = 50,
    reuse_counts: list = None
):
    """
    Benchmark performance for different max_env_reuse_count values.

    Args:
        base_url: Server base URL.
        num_tests: Tasks per configuration (should exceed max_env_reuse_count to see effect).
        reuse_counts: List of reuse counts to try.
    """
    if reuse_counts is None:
        reuse_counts = [5, 10, 20, 50, 100, 200]
    
    logger.info("=" * 100)
    logger.info("🧪 Testing max_env_reuse_count impact on performance")
    logger.info("=" * 100)
    
    # Same imports across tasks to maximize cache hits
    test_code_template = """
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem test_add_{idx} : ∀ n : ℕ, n + 0 = n := by
  intro n
  rw [Nat.add_zero]
"""
    
    # Same imports, distinct theorem names to avoid "already declared"
    test_codes = [test_code_template.format(idx=i) for i in range(num_tests)]
    
    logger.info(f"📝 Test setup:")
    logger.info(f"  - Tasks: {num_tests}")
    logger.info(f"  - Reuse counts: {reuse_counts}")
    logger.info(f"  - Same imports on all tasks (cache-friendly)")
    logger.info("")
    
    results = {}
    
    for reuse_count in reuse_counts:
        logger.info("=" * 100)
        logger.info(f"🔧 Testing max_env_reuse_count = {reuse_count}")
        logger.info("=" * 100)
        
        # 1. Update server config (requires restart)
        logger.warning(f"⚠️  Set MAX_ENV_REUSE_COUNT={reuse_count} and restart the server")
        logger.warning(f"   export MAX_ENV_REUSE_COUNT={reuse_count}")
        logger.warning(f"   Then press Enter to continue...")
        input()
        
        # 2. Wait for server to be ready
        logger.info("⏳ Waiting for server...")
        time.sleep(2)
        
        # 3. Clear cache
        try:
            requests.post(f"{base_url}/cache/clear", timeout=10)
            logger.info("✅ Cache cleared")
        except Exception as e:
            logger.error(f"❌ Failed to clear cache: {e}")
            continue
        
        # 4. Run benchmark
        logger.info(f"🚀 Running {num_tests} tasks...")
        
        start_time = time.time()
        
        try:
            response = requests.post(
                f"{base_url}/verify/batch",
                json={
                    "codes": test_codes,
                    "timeout": 60,
                    "max_retries": 2
                },
                timeout=600  # 10 minute timeout
            )
            response.raise_for_status()
            elapsed = time.time() - start_time
            
            data = response.json()
            processing_time = data.get("processing_time", elapsed)
            throughput = data.get("throughput", num_tests / elapsed)
            cache_stats = data.get("cache_stats", {})
            cpu_stats = data.get("cpu_stats", {})
            
            # Stats
            avg_time_per_task = processing_time / num_tests * 1000  # ms per task
            
            results[reuse_count] = {
                "total_time": processing_time,
                "avg_time_per_task_ms": avg_time_per_task,
                "throughput": throughput,
                "cache_hit_rate": cache_stats.get("hit_rate", "N/A"),
                "avg_cpu": cpu_stats.get("avg_cpu_percent", 0),
                "max_cpu": cpu_stats.get("max_cpu_percent", 0)
            }
            
            logger.info("")
            logger.info(f"📊 Results (max_env_reuse_count={reuse_count}):")
            logger.info(f"  - Total time: {processing_time:.2f}s")
            logger.info(f"  - Avg per task: {avg_time_per_task:.1f}ms")
            logger.info(f"  - Throughput: {throughput:.2f} tasks/s")
            logger.info(f"  - Cache hit rate: {cache_stats.get('hit_rate', 'N/A')}")
            logger.info(f"  - Avg CPU: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
            logger.info(f"  - Max CPU: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
            logger.info("")
            
        except requests.Timeout:
            logger.error(f"❌ Test timed out")
            results[reuse_count] = {"error": "timeout"}
        except Exception as e:
            logger.error(f"❌ Test failed: {e}")
            results[reuse_count] = {"error": str(e)}
    
    # 5. Summary comparison
    logger.info("=" * 100)
    logger.info("📊 Performance comparison summary")
    logger.info("=" * 100)
    logger.info("")
    
    # Table header
    logger.info(f"{'Reuse':<12} {'Total(s)':<12} {'Avg/task(ms)':<16} {'Throughput':<14} {'Cache hit':<12} {'Avg CPU%':<10}")
    logger.info("-" * 90)
    
    valid_results = {k: v for k, v in results.items() if "error" not in v}
    
    for reuse_count in reuse_counts:
        if reuse_count not in results:
            continue
        result = results[reuse_count]
        if "error" in result:
            logger.error(f"{reuse_count:<12} ERROR: {result['error']}")
        else:
            logger.info(
                f"{reuse_count:<12} "
                f"{result['total_time']:<12.2f} "
                f"{result['avg_time_per_task_ms']:<16.1f} "
                f"{result['throughput']:<14.2f} "
                f"{result['cache_hit_rate']:<12} "
                f"{result['avg_cpu']:<10.1f}"
            )
    
    logger.info("")
    
    # Best configuration
    if valid_results:
        best_reuse_count = min(valid_results.keys(), key=lambda k: valid_results[k]['avg_time_per_task_ms'])
        worst_reuse_count = max(valid_results.keys(), key=lambda k: valid_results[k]['avg_time_per_task_ms'])
        
        best_result = valid_results[best_reuse_count]
        worst_result = valid_results[worst_reuse_count]
        
        speedup = worst_result['avg_time_per_task_ms'] / best_result['avg_time_per_task_ms']
        
        logger.info("🏆 Conclusion:")
        logger.info(f"  - ✅ Best: max_env_reuse_count = {best_reuse_count}")
        logger.info(f"     Avg time: {best_result['avg_time_per_task_ms']:.1f}ms")
        logger.info(f"  - ❌ Worst: max_env_reuse_count = {worst_reuse_count}")
        logger.info(f"     Avg time: {worst_result['avg_time_per_task_ms']:.1f}ms")
        logger.info(f"  - 🚀 Speedup gap: {speedup:.2f}x")
        logger.info("")
        
        # Recommendations
        if best_reuse_count <= 20:
            logger.info("💡 Lower reuse counts look better; try 10–20")
        elif best_reuse_count >= 100:
            logger.info("💡 Higher reuse counts look better; 100 is already a solid choice")
        else:
            logger.info(f"💡 Set max_env_reuse_count = {best_reuse_count} for best results in this run")
    
    logger.info("=" * 100)
    
    return results


def test_reuse_count_performance_auto(
    base_url: str = "http://localhost:8000",
    num_tests: int = 100,
    test_file: str = "test/test_set.json"
):
    """
    Automated run: benchmark current config on a real dataset.

    Args:
        base_url: Server base URL.
        num_tests: Number of tasks to run.
        test_file: Path to test data JSON.
    """
    logger.info("=" * 100)
    logger.info("🧪 Auto mode: current max_env_reuse_count performance")
    logger.info("=" * 100)
    
    # Load test data
    test_path = Path(test_file)
    if not test_path.exists():
        logger.error(f"Test file not found: {test_file}")
        return False
    
    with open(test_path, 'r') as f:
        test_data = json.load(f)
    
    test_data = test_data[:num_tests]
    codes = [item['code'] for item in test_data]
    
    logger.info(f"📝 Test setup:")
    logger.info(f"  - Tasks: {len(codes)}")
    logger.info("")
    
    # Fetch current server config
    try:
        response = requests.get(f"{base_url}/")
        config = response.json()
        current_reuse_count = config.get("max_env_reuse_count", "unknown")
        logger.info(f"📊 Current server config:")
        logger.info(f"  - max_env_reuse_count: {current_reuse_count}")
        logger.info(f"  - max_cached_envs: {config.get('max_cached_envs', 'unknown')}")
        logger.info(f"  - num_workers: {config.get('num_workers', 'unknown')}")
        logger.info("")
    except Exception as e:
        logger.error(f"❌ Could not fetch server config: {e}")
        return False
    
    # Clear cache
    try:
        requests.post(f"{base_url}/cache/clear", timeout=10)
        logger.info("✅ Cache cleared")
    except Exception as e:
        logger.warning(f"⚠️  Failed to clear cache: {e}")
    
    # Run test
    logger.info(f"🚀 Starting test...")
    start_time = time.time()
    
    try:
        response = requests.post(
            f"{base_url}/verify/batch",
            json={
                "codes": codes,
                "timeout": 60,
                "max_retries": 2
            },
            timeout=600
        )
        response.raise_for_status()
        elapsed = time.time() - start_time
        
        data = response.json()
        processing_time = data.get("processing_time", elapsed)
        throughput = data.get("throughput", len(codes) / elapsed)
        cache_stats = data.get("cache_stats", {})
        cpu_stats = data.get("cpu_stats", {})
        results = data.get("results", [])
        
        # Stats
        valid_count = sum(1 for r in results if r.get("is_valid_no_sorry", False))
        avg_time_per_task = processing_time / len(codes) * 1000
        
        logger.info("")
        logger.info("=" * 100)
        logger.info("📊 Test results")
        logger.info("=" * 100)
        logger.info(f"⏱️  Performance:")
        logger.info(f"  - Total time: {processing_time:.2f}s ({processing_time/60:.1f} min)")
        logger.info(f"  - Avg per task: {avg_time_per_task:.1f}ms")
        logger.info(f"  - Throughput: {throughput:.2f} tasks/s")
        logger.info("")
        logger.info(f"🎯 Verification:")
        logger.info(f"  - Pass rate: {valid_count}/{len(results)} ({valid_count/len(results)*100:.1f}%)")
        logger.info("")
        logger.info(f"🎯 Cache:")
        logger.info(f"  - Hit rate: {cache_stats.get('hit_rate', 'N/A')}")
        logger.info(f"  - Hits: {cache_stats.get('total_hits', 0)}")
        logger.info(f"  - Misses: {cache_stats.get('total_misses', 0)}")
        logger.info("")
        logger.info(f"💻 CPU:")
        logger.info(f"  - Avg CPU: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
        logger.info(f"  - Max CPU: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
        logger.info("=" * 100)
        
        return True
        
    except Exception as e:
        logger.error(f"❌ Test failed: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return False


if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Benchmark max_env_reuse_count impact on performance")
    parser.add_argument("--mode", choices=["manual", "auto"], default="auto",
                        help="Mode: manual=compare several values (restarts), auto=current server config only")
    parser.add_argument("--base-url", default="http://localhost:8000", help="Server base URL")
    parser.add_argument("--num-tests", type=int, default=100, help="Number of tasks to run")
    parser.add_argument("--reuse-counts", type=int, nargs="+", default=[5, 10, 20, 50, 100],
                        help="Reuse counts to try (manual mode only)")
    
    args = parser.parse_args()
    
    if args.mode == "manual":
        logger.info("🔧 Manual mode: restart the server between reuse-count runs")
        test_reuse_count_performance(
            base_url=args.base_url,
            num_tests=args.num_tests,
            reuse_counts=args.reuse_counts
        )
    else:
        logger.info("🤖 Auto mode: benchmark current server configuration")
        test_reuse_count_performance_auto(
            base_url=args.base_url,
            num_tests=args.num_tests
        )

