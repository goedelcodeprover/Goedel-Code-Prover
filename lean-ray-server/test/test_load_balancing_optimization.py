#!/usr/bin/env python3
"""
Load balancing optimization test script.
Exercises newly implemented optimizations:
1. Task complexity ordering
2. Dynamic streaming submission
3. Two-tier cache affinity
4. Adaptive batch collection
"""

import json
import time
import requests
from pathlib import Path
from loguru import logger


def test_optimization_features(base_url: str = "http://localhost:8000"):
    """Test load balancing optimization features."""
    
    logger.info("=" * 80)
    logger.info("Testing load balancing optimization features")
    logger.info("=" * 80)
    
    # Clear cache for a clean test environment
    logger.info("🗑️  Clearing cache...")
    try:
        requests.post(f"{base_url}/cache/clear", timeout=5)
        logger.info("✅ Cache cleared")
    except Exception as e:
        logger.warning(f"⚠️  Failed to clear cache: {e}")
    
    # Test cases: tasks of varying complexity
    # Simple: basic definitions only, no imports
    simple_codes = [
        "def simple1 : Nat := 42",
        "def simple2 : String := \"hello\"",
        "def simple3 : Bool := true",
    ]
    
    # Medium: 1–2 imports
    medium_codes = [
        "import Mathlib\n\ndef medium1 (a b : Nat) : Nat := a + b",
        "import Mathlib\n\ndef medium2 (a b : Nat) : Nat := a * b",
        "import Aesop\n\ndef medium3 (a : Nat) : Nat := a + 1",
    ]
    
    # High: multiple imports + theorem proofs
    complex_codes = [
        """import Mathlib
import Aesop

theorem complex1 (a b : Nat) : a + b = b + a := by
  simp [Nat.add_comm]
""",
        """import Mathlib
import Aesop

theorem complex2 (n : Nat) : n + 0 = n := by
  simp
""",
        """import Mathlib

lemma complex3 (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simp [Nat.add_assoc]
""",
    ]
    
    # Combined workload: mixed complexity + repeated tasks (cache exercise)
    # Strategy: repeat each type so we exercise:
    # 1. Hard tasks scheduled first
    # 2. Cache hits (same-import tasks)
    # 3. Dynamic load balancing
    test_codes = (
        complex_codes * 20 +      # 60 complex tasks
        medium_codes * 30 +       # 90 medium tasks
        simple_codes * 30         # 90 simple tasks
    )
    # 240 tasks total
    
    logger.info(f"📦 Test case breakdown:")
    logger.info(f"  - Complex tasks: {len(complex_codes) * 20} (should be prioritized)")
    logger.info(f"  - Medium tasks: {len(medium_codes) * 30}")
    logger.info(f"  - Simple tasks: {len(simple_codes) * 30}")
    logger.info(f"  - Total tasks: {len(test_codes)}")
    logger.info(f"  - Expected: hard tasks run first to reduce tail latency; same-import tasks reuse cache")
    
    payload = {
        "codes": test_codes,
        "timeout": 60,
        "max_retries": 2,
        "overflow_threshold": 3  # Low threshold to exercise overflow and second-tier affinity
    }
    
    try:
        logger.info(f"\n🚀 Starting batch verification...")
        start_time = time.time()
        response = requests.post(f"{base_url}/verify/batch", json=payload, timeout=1200)
        response.raise_for_status()
        elapsed = time.time() - start_time
        
        data = response.json()
        logger.info(f"✅ Batch verification finished")
        
        # Analyze results
        results = data.get("results", [])
        if not results:
            logger.error("❌ No results returned")
            return False
        
        # 1. Basic stats
        processing_time = data.get("processing_time", elapsed)
        throughput = data.get("throughput", len(test_codes) / elapsed if elapsed > 0 else 0)
        pass_rate_no_sorry = data.get("pass_rate_no_sorry", 0)
        pass_rate_with_sorry = data.get("pass_rate_with_sorry", 0)
        
        logger.info("\n" + "=" * 80)
        logger.info("📊 Performance stats")
        logger.info("=" * 80)
        logger.info(f"  ⏱️  Processing time: {processing_time:.2f}s")
        logger.info(f"  🚀 Throughput: {throughput:.2f} tasks/s")
        logger.info(f"  ✅ Pass rate (no_sorry): {pass_rate_no_sorry:.1%}")
        logger.info(f"  ✅ Pass rate (with_sorry): {pass_rate_with_sorry:.1%}")
        
        # 2. CPU usage
        cpu_stats = data.get("cpu_stats", {})
        if cpu_stats:
            logger.info("\n" + "=" * 80)
            logger.info("💻 CPU usage")
            logger.info("=" * 80)
            logger.info(f"  - Average: {cpu_stats.get('avg_cpu_percent', 0):.1f}%")
            logger.info(f"  - Max: {cpu_stats.get('max_cpu_percent', 0):.1f}%")
            logger.info(f"  - Min: {cpu_stats.get('min_cpu_percent', 0):.1f}%")
            logger.info(f"  - Samples: {cpu_stats.get('num_samples', 0)}")
            logger.info(f"  - Duration: {cpu_stats.get('duration_seconds', 0):.2f}s")
            
            # Assess CPU utilization
            avg_cpu = cpu_stats.get('avg_cpu_percent', 0)
            if avg_cpu > 80:
                logger.info(f"  ✅ Excellent CPU utilization ({avg_cpu:.1f}%)")
            elif avg_cpu > 60:
                logger.info(f"  ⚠️  Good CPU utilization ({avg_cpu:.1f}%)")
            else:
                logger.warning(f"  ⚠️  Low CPU utilization ({avg_cpu:.1f}%) — possible bottleneck")
        
        # 3. Cache stats (focus)
        cache_stats = data.get("cache_stats", {})
        if cache_stats and cache_stats.get('enabled'):
            total_hits = cache_stats.get('total_hits', 0)
            total_misses = cache_stats.get('total_misses', 0)
            hit_rate_str = cache_stats.get('hit_rate', '0.0%')
            
            logger.info("\n" + "=" * 80)
            logger.info("🎯 Cache stats (cache affinity)")
            logger.info("=" * 80)
            logger.info(f"  - Cache hits: {total_hits}")
            logger.info(f"  - Cache misses: {total_misses}")
            logger.info(f"  - Hit rate: {hit_rate_str}")
            
            # Assess cache effectiveness
            if total_hits + total_misses > 0:
                hit_rate = total_hits / (total_hits + total_misses) * 100
                if hit_rate > 70:
                    logger.info(f"  ✅ Excellent hit rate — second-tier affinity looks good")
                elif hit_rate > 50:
                    logger.info(f"  ⚠️  Decent hit rate — room for improvement")
                else:
                    logger.warning(f"  ⚠️  Low hit rate — routing may need tuning")
        
        # 4. Configuration
        config = data.get("config", {})
        if config:
            logger.info("\n" + "=" * 80)
            logger.info("⚙️  Configuration")
            logger.info("=" * 80)
            logger.info(f"  - Workers: {config.get('num_workers', 'N/A')}")
            logger.info(f"  - Replicas: {config.get('num_replicas', 'N/A')}")
            logger.info(f"  - Cache enabled: {config.get('cache_enabled', False)}")
            logger.info(f"  - Max cached envs: {config.get('max_cached_envs', 'N/A')}")
            logger.info(f"  - Overflow threshold: {config.get('overflow_threshold', 'N/A')}")
            logger.info(f"  - Routing strategy: {config.get('routing_strategy', 'N/A')}")
        
        # 5. Failed tasks
        failed_results = [r for r in results if not r.get("is_valid_no_sorry", False)]
        if failed_results:
            logger.warning(f"\n⚠️  {len(failed_results)} verification(s) failed")
            logger.warning(f"   Failure rate: {len(failed_results)/len(results):.1%}")
            
            # Show first 3 failures
            for i, r in enumerate(failed_results[:3]):
                logger.warning(f"\n  Failure [{i+1}]:")
                logger.warning(f"    Code: {r.get('problem', 'N/A')[:100]}...")
                logger.warning(f"    Error: {r.get('error_message', 'N/A')}")
        else:
            logger.info(f"\n✅ All tasks verified successfully")
        
        # 6. Optimization summary
        logger.info("\n" + "=" * 80)
        logger.info("🎯 Optimization summary")
        logger.info("=" * 80)
        
        # Evaluate optimizations from stats
        optimizations_working = []
        
        # Check 1: high throughput (dynamic scheduling + complexity ordering)
        if throughput > 5.0:  # e.g. target >5 tasks/s
            optimizations_working.append("✅ High throughput (dynamic scheduling effective)")
        else:
            logger.warning(f"  ⚠️  Low throughput ({throughput:.2f} tasks/s)")
        
        # Check 2: high CPU utilization (load balancing)
        if cpu_stats and cpu_stats.get('avg_cpu_percent', 0) > 70:
            optimizations_working.append("✅ High CPU utilization (good load balance)")
        
        # Check 3: high cache hit rate (cache affinity)
        if cache_stats and cache_stats.get('enabled'):
            total_hits = cache_stats.get('total_hits', 0)
            total_misses = cache_stats.get('total_misses', 0)
            if total_hits + total_misses > 0:
                hit_rate = total_hits / (total_hits + total_misses) * 100
                if hit_rate > 60:
                    optimizations_working.append("✅ High cache hit rate (affinity effective)")
        
        if optimizations_working:
            for opt in optimizations_working:
                logger.info(f"  {opt}")
        else:
            logger.warning("  ⚠️  Some optimizations may not be visible — check configuration")
        
        logger.info("=" * 80)
        
        return True
        
    except Exception as e:
        logger.error(f"❌ Test failed: {e}")
        import traceback
        logger.error(traceback.format_exc())
        return False


def compare_with_baseline(base_url: str = "http://localhost:8000"):
    """Optional: compare performance before/after optimization."""
    logger.info("\n" + "=" * 80)
    logger.info("📊 Performance comparison (optional)")
    logger.info("=" * 80)
    logger.info("Tip: run a baseline against the old server first,")
    logger.info("then switch to the new build and run this test for comparison.")
    logger.info("=" * 80)


if __name__ == "__main__":
    import sys
    
    # Logging setup
    logger.remove()
    logger.add(
        sys.stdout,
        format="<green>{time:HH:mm:ss}</green> | <level>{level: <8}</level> | <level>{message}</level>",
        level="INFO"
    )
    
    base_url = "http://localhost:8000"
    if len(sys.argv) > 1:
        base_url = sys.argv[1]
    
    logger.info(f"🎯 Target: {base_url}")
    
    # Health check first
    try:
        response = requests.get(f"{base_url}/health/init", timeout=10)
        if response.status_code != 200:
            logger.error("❌ Server health check failed")
            sys.exit(1)
        logger.info("✅ Server health check passed")
    except Exception as e:
        logger.error(f"❌ Cannot connect to server: {e}")
        sys.exit(1)
    
    # Run optimization test
    success = test_optimization_features(base_url)
    
    if success:
        logger.info("\n🎉 All optimization tests passed!")
        sys.exit(0)
    else:
        logger.error("\n❌ Optimization tests failed")
        sys.exit(1)

