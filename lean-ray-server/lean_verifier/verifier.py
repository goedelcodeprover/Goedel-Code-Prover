from lean_verifier.leanrepl import LeanREPL
from lean_verifier.utils import (
    parse_client_response, 
    has_error_response,
    parse_verification_results,
    parse_verification_error_results
)
from lean_verifier.config import settings

from typing import List, Dict, Optional
import ray
from tqdm import tqdm
from loguru import logger


class LeanVerifier:
    """
    Lean code verifier with REPL caching support.
    
    Features:
    - Enable/disable REPL environment caching
    - Ray Actor-based persistent REPL pool
    - Batch verification with load balancing
    - Cache statistics and monitoring
    """
    
    def __init__(self, enable_cache: bool = True, max_cached_envs: int = 5):
        """
        Initialize LeanVerifier
        
        Args:
            enable_cache: Whether to enable REPL environment caching
            max_cached_envs: Maximum number of cached environments per REPL
        """
        self._initialized = False
        self.enable_cache = enable_cache
        self.max_cached_envs = max_cached_envs
        self.repl_actors = []
        
    def initialize(self):
        """Manually initialize Ray (alternative to context manager)"""
        if not self._initialized:
            # Check if Ray is already initialized
            if not ray.is_initialized():
                try:
                    ray.init(num_cpus=settings.MAX_REPLS)
                    max_repl_memory = (
                        ray.cluster_resources()["memory"] 
                        * settings.REPL_MEMORY_RATIO 
                        / settings.MAX_REPLS
                    )
                except ValueError:
                    logger.warning(
                        "Connecting to existing cluster without specifying resources"
                    )
                    ray.init()
                    max_repl_memory = (
                        ray.cluster_resources()["memory"] 
                        * settings.REPL_MEMORY_RATIO 
                        / ray.cluster_resources()["CPU"]
                    )
            else:
                # Ray already initialized
                max_repl_memory = (
                    ray.cluster_resources()["memory"] 
                    * settings.REPL_MEMORY_RATIO 
                    / ray.cluster_resources().get("CPU", settings.MAX_REPLS)
                )
            
            self._initialized = True
            
            if self.enable_cache:
                logger.info(f"🎯 Initializing {settings.MAX_REPLS} cached REPL actors")
                self._initialize_cached_actors(max_repl_memory)
            else:
                logger.info(f"📦 Initializing stateless REPL workers")
                self._initialize_stateless_workers(max_repl_memory)
    
    def _initialize_cached_actors(self, max_repl_memory: float):
        """Initialize Ray Actors with persistent REPL caching."""
        
        @ray.remote(memory=max_repl_memory)
        class CachedREPLActor:
            """Persistent REPL Actor with environment caching."""
            
            def __init__(self, enable_cache: bool, max_cached_envs: int):
                self.repl = LeanREPL(
                    enable_cache=enable_cache, 
                    max_cached_envs=max_cached_envs
                )
                self.verification_count = 0
            
            def verify(self, code: str, timeout: int, max_retries: int = 2):
                """Verify code using cached REPL."""
                self.verification_count += 1
                response = {}
                try:
                    response["response"] = self.repl.one_pass_verify(
                        code, timeout, max_retries=max_retries
                    )
                    response["error"] = None
                except Exception as e:
                    response["response"] = None
                    response["error"] = str(e)
                return response
            
            def get_stats(self):
                """Get REPL cache statistics."""
                stats = self.repl.get_cache_stats()
                stats["verification_count"] = self.verification_count
                return stats
            
            def clear_cache(self):
                """Clear REPL environment cache."""
                self.repl.clear_cache()
            
            def shutdown(self):
                """Shutdown REPL process."""
                self.repl.close()
        
        # Create actor pool
        self.repl_actors = [
            CachedREPLActor.remote(self.enable_cache, self.max_cached_envs)
        ]
        self._actor_class = CachedREPLActor
        logger.info(f"✅ Created {len(self.repl_actors)} cached REPL actors")
    
    def _initialize_stateless_workers(self, max_repl_memory: float):
        """Initialize stateless Ray workers (original behavior)."""
        
        @ray.remote(memory=max_repl_memory)
        def _verify_single(code, timeout, max_retries=2):
            repl = LeanREPL(enable_cache=False)
            response = {}
            try:
                response["response"] = repl.one_pass_verify(
                    code, timeout, max_retries=max_retries
                )
                response["error"] = None
            except Exception as e:
                response["response"] = None
                response["error"] = str(e)
            repl.close()
            return response
        
        self._verify_single_remote = _verify_single
        logger.info(f"✅ Created stateless worker function")
    
    def shutdown(self):
        """Shutdown Ray cluster and cleanup resources"""
        if self._initialized:
            if self.enable_cache and self.repl_actors:
                logger.info("🧹 Shutting down REPL actors...")
                # Gracefully shutdown all actors
                ray.get([actor.shutdown.remote() for actor in self.repl_actors])
            
            ray.shutdown()
            self._initialized = False
            logger.info("✅ Ray cluster shutdown complete")
            
    def __enter__(self):
        """Context manager entry point - initialize Ray"""
        if not self._initialized:
            self.initialize()
        return self
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit point - cleanup Ray resources"""
        self.shutdown()
        
    def verify_batch(
        self, 
        codes: List[str], 
        timeout: int = 60, 
        use_tqdm: bool = False, 
        max_retries: int = 2
    ) -> List[Dict]:
        """
        Batch verify Lean code with load balancing across REPL pool.
        
        Args:
            codes: List of Lean code strings
            timeout: Timeout in seconds per verification
            use_tqdm: Show progress bar
            max_retries: Maximum number of retries for each task
            
        Returns:
            List of verification results with same order as input
        """
        if not self._initialized:
            raise RuntimeError(
                "LeanVerifier must be used as a context manager or initialized manually"
            )
        
        results = [None] * len(codes)
        
        if self.enable_cache:
            # Use actor pool with round-robin load balancing
            obj_dict = {}
            for i, code in enumerate(codes):
                # Round-robin: distribute codes evenly across actors
                actor = self.repl_actors[i % len(self.repl_actors)]
                obj_ref = actor.verify.remote(code, timeout, max_retries)
                obj_dict[obj_ref] = i
            
            logger.info(
                f"📤 Submitted {len(codes)} tasks to {len(self.repl_actors)} actors"
            )
        else:
            # Use stateless workers
            obj_dict = {
                self._verify_single_remote.remote(code, timeout, max_retries): i 
                for i, code in enumerate(codes)
            }
            logger.info(f"📤 Submitted {len(codes)} tasks to stateless workers")
        
        # Collect results
        if use_tqdm:
            pbar = tqdm(total=len(codes), desc="Verifying Lean code")
        
        remaining = list(obj_dict.keys())
        while remaining:
            done, remaining = ray.wait(remaining, num_returns=1)
            result = ray.get(done[0])
            original_index = obj_dict[done[0]]
            results[original_index] = result
            
            if use_tqdm:
                pbar.update(1)
        
        if use_tqdm:
            pbar.close()
        
        logger.info(f"✅ Completed {len(codes)} verifications")
        return results
    
    def verify_single(
        self, 
        code: str, 
        timeout: int = 60, 
        max_retries: int = 2
    ) -> Dict:
        """
        Verify a single Lean code.
        
        Uses cached REPL actor if available, otherwise creates temporary REPL.
        For batch operations, use verify_batch() for better performance.
        """
        # Use REPL actor if caching is enabled and actors exist
        if self.enable_cache and self.repl_actors:
            try:
                # Use the first (and only) REPL actor in the pool
                actor = self.repl_actors[0]
                obj_ref = actor.verify.remote(code, timeout, max_retries)
                result = ray.get(obj_ref)
                return result
            except Exception as e:
                logger.warning(f"Failed to use REPL actor, falling back to temporary REPL: {e}")
        
        # Fallback: create temporary REPL (no caching benefits)
        repl = LeanREPL(enable_cache=self.enable_cache)
        response = {}
        try:
            response["response"] = repl.one_pass_verify(
                code, timeout, max_retries=max_retries
            )
            response["error"] = None
        except Exception as e:
            response["response"] = None
            response["error"] = str(e)
        repl.close()
        return response
    
    def get_cache_stats(self) -> List[Dict]:
        """
        Get cache statistics from all REPL actors.
        
        Returns:
            List of stats dictionaries, one per actor
        """
        if not self.enable_cache or not self.repl_actors:
            logger.warning("Cache not enabled or actors not initialized")
            return []
        
        stats_list = ray.get([actor.get_stats.remote() for actor in self.repl_actors])
        
        # Calculate aggregate statistics
        total_hits = sum(s["cache_hits"] for s in stats_list)
        total_misses = sum(s["cache_misses"] for s in stats_list)
        total_requests = total_hits + total_misses
        overall_hit_rate = (
            (total_hits / total_requests * 100) if total_requests > 0 else 0
        )
        
        logger.info(f"📊 Cache Stats Summary:")
        logger.info(f"   Total Hits: {total_hits}")
        logger.info(f"   Total Misses: {total_misses}")
        logger.info(f"   Overall Hit Rate: {overall_hit_rate:.1f}%")
        
        return stats_list
    
    def clear_all_caches(self):
        """Clear environment caches in all REPL actors."""
        if not self.enable_cache or not self.repl_actors:
            logger.warning("Cache not enabled or actors not initialized")
            return
        
        ray.get([actor.clear_cache.remote() for actor in self.repl_actors])
        logger.info(f"🗑️  Cleared caches in {len(self.repl_actors)} actors")
    
    def parse_results(self, response: List[Dict]) -> List[Dict]:
        """
        Parse the response from the LeanREPL
        
        Args:
            response: Response from the LeanREPL
            
        Returns:
            Parsed results
        
        Note: This method is deprecated. Use utils.parse_verification_results() instead.
        """
        return parse_verification_results(response)

    def parse_error_results(self, response: List[Dict]) -> List[Dict]:
        """
        Parse the error results from the LeanREPL's response
        
        Args:
            response: Response from the LeanREPL
            
        Returns:
            List of (has_error, error_messages) tuples
        
        Note: This method is deprecated. Use utils.parse_verification_error_results() instead.
        """
        return parse_verification_error_results(response)


# Usage examples
if __name__ == "__main__":
    # Example 1: Cached verification (recommended for batch jobs)
    print("=" * 60)
    print("Example 1: Batch verification WITH caching")
    print("=" * 60)
    
    with LeanVerifier(enable_cache=True, max_cached_envs=10) as verifier:
        codes1 = [
            "import Mathlib\ntheorem t1 : 1 + 1 = 2 := rfl",
            "import Mathlib\ntheorem t2 : 2 + 2 = 4 := rfl",  # Same header!
        ]
        codes2 = [
            "import Mathlib\ntheorem t3 : 3 + 3 = 6 := rfl",  # Same header!
            "import Aesop\ntheorem t4 : True := trivial",      # Different header
        ]
        
        results1 = verifier.verify_batch(codes1, timeout=60, use_tqdm=True)
        results2 = verifier.verify_batch(codes2, timeout=60, use_tqdm=True)
        
        # Check results
        for i, result in enumerate(results1 + results2):
            if result["error"]:
                print(f"Code {i}: ERROR - {result['error']}")
            else:
                print(f"Code {i}: SUCCESS")
        
        # Show cache performance
        print("\n📊 Cache Performance:")
        stats = verifier.get_cache_stats()
        for i, stat in enumerate(stats):
            print(f"  Actor {i}: {stat['hit_rate']} hit rate, "
                  f"{stat['verification_count']} verifications")
    
    print("\n" + "=" * 60)
    print("Example 2: Batch verification WITHOUT caching (original)")
    print("=" * 60)
    
    with LeanVerifier(enable_cache=False) as verifier:
        codes = [
            "import Mathlib\ntheorem t1 : 1 + 1 = 2 := rfl",
            "import Mathlib\ntheorem t2 : 2 + 2 = 4 := rfl",
        ]
        
        results = verifier.verify_batch(codes, timeout=60, use_tqdm=True)
        print(f"✅ Completed {len(results)} verifications (no caching)")
    
    print("\n" + "=" * 60)
    print("Example 3: Single verification")
    print("=" * 60)
    
    with LeanVerifier(enable_cache=True) as verifier:
        code = "import Mathlib\ntheorem test : 1 + 1 = 2 := rfl"
        result = verifier.verify_single(code, timeout=60)
        
        if result["error"]:
            print(f"ERROR: {result['error']}")
        else:
            print(f"SUCCESS: {result['response']}")