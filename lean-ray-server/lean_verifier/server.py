"""
Ray Serve server implementation for Lean code verification with REPL caching
Features: Multiple replicas + Shared cached REPL workers + Environment reuse
"""

import asyncio
import time
import threading
from typing import List, Dict, Any, Optional, Tuple
from contextlib import asynccontextmanager
import os

import ray
from ray import serve
from fastapi import FastAPI, HTTPException, BackgroundTasks
from fastapi.responses import JSONResponse
from pydantic import BaseModel, Field
from loguru import logger

from lean_verifier.verifier import LeanVerifier
from lean_verifier.leanrepl import LeanREPL
from lean_verifier.utils import (
    parse_verification_results, 
    parse_verification_error_results,
    extract_code_header_hash,
    estimate_task_complexity
)
from lean_verifier.config import settings


# ============ Resource Monitor ============
class ResourceMonitor:
    """Real-time system resource monitor for Ray cluster
    
    Monitors:
    - Actual CPU utilization (via psutil, not Ray's reserved resources)
    - Ray resource allocation (reserved vs available)
    - Active task count (actual workload)
    """
    
    def __init__(self, interval: float = 1.0):
        self.interval = interval
        self.samples = []
        self.monitoring = False
        self.thread = None
        self.start_time = None
        
        # Try to import psutil for real CPU monitoring
        try:
            import psutil
            self.psutil = psutil
            self.has_psutil = True
        except ImportError:
            self.psutil = None
            self.has_psutil = False
    
    def start(self):
        """Start monitoring"""
        self.samples = []
        self.monitoring = True
        self.start_time = time.time()
        
        def monitor():
            while self.monitoring:
                sample = {
                    'timestamp': time.time() - self.start_time,
                }
                
                # 1. Real CPU utilization (if psutil available)
                if self.has_psutil:
                    try:
                        # Get per-CPU utilization and average
                        cpu_percent = self.psutil.cpu_percent(interval=0.1)
                        sample['cpu_percent_real'] = cpu_percent
                    except Exception:
                        sample['cpu_percent_real'] = 0.0
                else:
                    sample['cpu_percent_real'] = None
                
                # 2. Ray resource allocation (for comparison)
                try:
                    total_cpu = ray.cluster_resources().get("CPU", 0)
                    available_cpu = ray.available_resources().get("CPU", 0)
                    reserved_cpu = total_cpu - available_cpu
                    reserved_percent = (reserved_cpu / total_cpu * 100) if total_cpu > 0 else 0
                    
                    sample['ray_reserved_cpu'] = reserved_cpu
                    sample['ray_available_cpu'] = available_cpu
                    sample['ray_reserved_percent'] = reserved_percent
                except Exception:
                    sample['ray_reserved_cpu'] = 0
                    sample['ray_available_cpu'] = 0
                    sample['ray_reserved_percent'] = 0
                
                # 3. Memory usage (if psutil available)
                if self.has_psutil:
                    try:
                        mem = self.psutil.virtual_memory()
                        sample['memory_percent'] = mem.percent
                        sample['memory_used_gb'] = mem.used / (1024**3)
                    except Exception:
                        sample['memory_percent'] = 0
                        sample['memory_used_gb'] = 0
                else:
                    sample['memory_percent'] = None
                    sample['memory_used_gb'] = None
                
                self.samples.append(sample)
                time.sleep(self.interval)
        
        self.thread = threading.Thread(target=monitor, daemon=True)
        self.thread.start()
    
    def stop(self):
        """Stop monitoring and return statistics"""
        self.monitoring = False
        if self.thread:
            self.thread.join(timeout=2.0)
        
        if not self.samples:
            return {
                'avg_cpu_real': 0.0,
                'max_cpu_real': 0.0,
                'min_cpu_real': 0.0,
                'avg_ray_reserved': 0.0,
                'samples': 0,
                'has_real_cpu_data': False
            }
        
        # Extract statistics
        stats = {
            'samples': len(self.samples),
            'duration': time.time() - self.start_time,
            'has_real_cpu_data': self.has_psutil,
            'timeline': self.samples
        }
        
        # Real CPU stats (if available)
        if self.has_psutil:
            cpu_real_values = [s['cpu_percent_real'] for s in self.samples if s.get('cpu_percent_real') is not None]
            if cpu_real_values:
                stats['avg_cpu_real'] = sum(cpu_real_values) / len(cpu_real_values)
                stats['max_cpu_real'] = max(cpu_real_values)
                stats['min_cpu_real'] = min(cpu_real_values)
            
            # Memory stats
            mem_values = [s['memory_percent'] for s in self.samples if s.get('memory_percent') is not None]
            if mem_values:
                stats['avg_memory_percent'] = sum(mem_values) / len(mem_values)
                stats['max_memory_percent'] = max(mem_values)
        
        # Ray reserved CPU stats (for comparison)
        ray_reserved_values = [s['ray_reserved_percent'] for s in self.samples]
        if ray_reserved_values:
            stats['avg_ray_reserved_percent'] = sum(ray_reserved_values) / len(ray_reserved_values)
            stats['max_ray_reserved_percent'] = max(ray_reserved_values)
            stats['min_ray_reserved_percent'] = min(ray_reserved_values)
        
        return stats


# ============ Global Shared Cached Workers ============
# Workers are now managed as Ray named actors (truly global across all replicas)
# No need for process-level global variables or locks


def get_or_create_global_workers(
    num_workers: int = None, 
    enable_cache: bool = True,
    max_cached_envs: int = 3,
    max_env_reuse_count: int = 12
):
    """Get or create globally shared workers with REPL caching using Ray named actors
    
    Key design:
    - Workers created as Ray named actors (truly global across all replicas)
    - All replicas share the same worker pool (no duplication)
    - Workers persist even if replica restarts (lifetime="detached")
    - Intelligent routing: same imports -> same worker (cache affinity)
    - Each worker maintains its own environment cache (3 is enough with intelligent routing)
    
    Args:
        num_workers: Number of workers
        enable_cache: Whether to enable REPL environment caching
        max_cached_envs: Maximum cached environments per worker (default 3 is optimal with intelligent routing)
        max_env_reuse_count: Maximum reuse count per environment (prevents memory leaks)
    """
    if num_workers is None:
        num_workers = settings.WORKER_POOL_SIZE
    
    cache_status = "WITH caching" if enable_cache else "WITHOUT caching"
    
    workers = []
    workers_created = 0
    workers_reused = 0
    
    logger.info(f"🔧 Getting or creating {num_workers} GLOBAL workers {cache_status}")
    
    # Try to get or create each worker by name
    for i in range(num_workers):
        worker_name = f"lean_worker_{i}"
        try:
            # Try to get existing worker
            worker = ray.get_actor(worker_name)
            workers.append(worker)
            workers_reused += 1
        except ValueError:
            # Worker doesn't exist, create new one
            worker = CachedLeanVerifierWorker.options(
                name=worker_name,
                lifetime="detached",  # Persist across replica restarts
                get_if_exists=True  # Avoid race condition between replicas
            ).remote(enable_cache, max_cached_envs, max_env_reuse_count)
            workers.append(worker)
            workers_created += 1
    
    # Initialize newly created workers in parallel
    if workers_created > 0:
        logger.info(f"⏳ Initializing {workers_created} new workers in parallel...")
        init_futures = []
        for i, worker in enumerate(workers):
            # Only initialize workers we just created (check by trying to get actor by index)
            if i >= workers_reused:
                init_futures.append(worker.initialize.remote())
        
        if init_futures:
            ray.get(init_futures)
    
    logger.info(
        f"✅ {num_workers} GLOBAL workers ready! "
        f"(Reused: {workers_reused}, Created: {workers_created})"
    )
    
    return workers


# Ray remote worker with REPL caching
@ray.remote(num_cpus=settings.WORKER_CPU_PER_TASK)  # CPUs reserved per worker (configurable)
class CachedLeanVerifierWorker:
    """Ray remote worker with persistent REPL and environment caching"""
    
    def __init__(self, enable_cache: bool = True, max_cached_envs: int = 10, max_env_reuse_count: int = 100):
        self.repl = None
        self._initialized = False
        self.enable_cache = enable_cache
        self.max_cached_envs = max_cached_envs
        self.max_env_reuse_count = max_env_reuse_count
        self.verification_count = 0
        
    def initialize(self):
        """Initialize REPL with caching in remote worker"""
        if not self._initialized:
            try:
                # Create a persistent REPL directly (no nested Ray actors!)
                self.repl = LeanREPL(
                    enable_cache=self.enable_cache,
                    max_cached_envs=self.max_cached_envs,
                    max_env_reuse_count=self.max_env_reuse_count
                )
                self._initialized = True
                return True
            except Exception as e:
                print(f"Failed to initialize LeanREPL in worker: {e}")
                return False
        return True
    
    def verify_single(self, code: str, timeout: int, max_retries: int = 2) -> Dict:
        """Verify single code using cached REPL
        
        Returns:
            Dict with "response" and "error" keys (raw format for parsing)
        """
        if not self._initialized:
            if not self.initialize():
                return {
                    "response": None,
                    "error": "Worker not initialized"
                }
        
        self.verification_count += 1
        
        try:
            # Use LeanREPL directly
            response = self.repl.one_pass_verify(code, timeout, max_retries=max_retries)
            return {
                "response": response,
                "error": None
            }
        except Exception as e:
            return {
                "response": None,
                "error": str(e)
            }
    
    def get_cache_stats(self) -> Dict:
        """Get REPL cache statistics from this worker"""
        if not self._initialized or not self.repl:
            return {
                "error": "Worker not initialized",
                "verification_count": 0
            }
        
        try:
            stats = self.repl.get_cache_stats()
            stats["verification_count"] = self.verification_count
            return stats
        except Exception as e:
            return {
                "error": str(e),
                "verification_count": self.verification_count
            }
    
    def clear_cache(self):
        """Clear REPL environment cache"""
        if self._initialized and self.repl:
            self.repl.clear_cache()
    
    def shutdown(self):
        """Shutdown REPL"""
        if self._initialized and self.repl:
            self.repl.close()


# Request and Response Models
class VerifyRequest(BaseModel):
    """Single verification request"""
    code: str = Field(..., description="Lean code to verify")
    timeout: int = Field(default=60, description="Timeout in seconds")
    max_retries: int = Field(default=2, description="Maximum number of retries")


class BatchVerifyRequest(BaseModel):
    """Batch verification request"""
    codes: List[str] = Field(..., description="List of Lean codes to verify")
    timeout: int = Field(default=60, description="Timeout in seconds")
    max_retries: int = Field(default=2, description="Maximum number of retries")
    overflow_threshold: Optional[int] = Field(
        default=None,
        description="Min tasks per worker before overflow (uses server default if None). "
                    "Actual threshold = max(avg_load, this value). Lower = more parallelism, Higher = more cache hits."
    )


class VerificationResult(BaseModel):
    """Verification result"""
    problem: str
    is_valid_no_sorry: bool
    is_valid_with_sorry: bool
    error_message: Optional[Tuple[bool, List]] = None
    response: Optional[Dict] = None


class BatchVerificationResponse(BaseModel):
    """Batch verification response"""
    results: List[VerificationResult]
    total: int
    pass_rate_no_sorry: float
    pass_rate_with_sorry: float
    processing_time: float = Field(description="Processing time in seconds")
    throughput: float = Field(description="Tasks per second")
    cpu_stats: Optional[Dict[str, Any]] = Field(default=None, description="CPU utilization statistics")
    cache_stats: Optional[Dict[str, Any]] = Field(default=None, description="REPL cache statistics")
    config: Optional[Dict[str, Any]] = Field(default=None, description="Processing configuration used")


class CacheStatsResponse(BaseModel):
    """Cache statistics response"""
    workers: List[Dict[str, Any]] = Field(description="Per-worker cache statistics")
    aggregate: Dict[str, Any] = Field(description="Aggregate statistics")


# FastAPI app for ingress
app = FastAPI(
    title="Lean Verifier Server (Ray Native + REPL Caching)",
    description="High-performance Lean code verification service with REPL environment caching",
    version="3.0.0"
)


# Ray Serve service class with FastAPI ingress
@serve.deployment(
    num_replicas=settings.SERVE_NUM_REPLICAS,
    ray_actor_options={"num_cpus": settings.REPLICA_CPU_PER_TASK}
)
@serve.ingress(app)
class LeanVerifierService:
    """Lean verification service with REPL caching and intelligent routing
    
    Architecture (360 cores example):
    - Multiple replicas (8-16): Handle concurrent HTTPS requests
    - Shared cached worker pool (320): Persistent REPLs with environment caching
    - Intelligent routing: Same imports -> same worker (cache affinity)
    - Ray native scheduling: Dynamic load balancing
    
    Advantages:
    ✅ Support multiple concurrent batch requests
    ✅ REPL environment caching (10x faster for same imports)
    ✅ Intelligent routing maximizes cache hit rate (based on header hash)
    ✅ Workers globally shared, no duplication
    ✅ Ray automatic load balancing
    ✅ High resource utilization
    """
    
    def __init__(self):
        # Reconfigure logger
        from loguru import logger as actor_logger
        actor_logger.remove()
        actor_logger.add(
            lambda msg: print(msg, end=""),
            level="INFO",
            format="<green>{time:YYYY-MM-DD HH:mm:ss}</green> | <level>{level: <8}</level> | <cyan>{name}</cyan>:<cyan>{function}</cyan>:<cyan>{line}</cyan> - <level>{message}</level>"
        )
        self.logger = actor_logger
        
        # Get configuration
        self.worker_pool_size = settings.WORKER_POOL_SIZE
        self.num_replicas = settings.SERVE_NUM_REPLICAS
        self.replica_cpu_per_task = settings.REPLICA_CPU_PER_TASK
        self.enable_cache = settings.ENABLE_REPL_CACHE
        self.max_cached_envs = settings.MAX_CACHED_ENVS
        self.max_env_reuse_count = settings.MAX_ENV_REUSE_COUNT
        self.overflow_threshold = settings.OVERFLOW_THRESHOLD
        
        available_resources = ray.available_resources()
        available_cpus = available_resources["CPU"]
        available_memory = available_resources["memory"] / (1024**3)
        
        # Resource validation
        # Reserve CPU for: replicas + system tasks + dynamic scheduling buffer
        safe_buffer = 8  # Extra buffer for Ray task scheduling
        replicas_cpu_needed = self.num_replicas * self.replica_cpu_per_task
        
        # Calculate max workers based on CPU allocation per task
        # If WORKER_CPU_PER_TASK=0.5 → 1/0.5=2.0 workers per CPU
        # If WORKER_CPU_PER_TASK=1.0 → 1/1.0=1.0 workers per CPU
        max_safe_workers = int((available_cpus - replicas_cpu_needed - safe_buffer) / settings.WORKER_CPU_PER_TASK)
        
        if self.worker_pool_size > max_safe_workers:
            self.logger.warning(
                f"Worker pool size ({self.worker_pool_size}) exceeds safe limit ({max_safe_workers}). "
            )
            self.worker_pool_size = max_safe_workers
            self.logger.info(f"Adjusted worker pool size to {self.worker_pool_size}")
        
        estimated_memory_needed = self.worker_pool_size * settings.REPL_MEMORY_LIMIT_GB
        if estimated_memory_needed > available_memory:
            self.logger.warning(
                f"Memory need ({estimated_memory_needed}GB) > available ({available_memory}GB)"
            )
            self.worker_pool_size = min(
                self.worker_pool_size, 
                int(available_memory * 0.8 / settings.REPL_MEMORY_LIMIT_GB)
            )
            self.logger.info(f"Adjusted worker pool size to {self.worker_pool_size}")
        
        cache_status = "ENABLED" if self.enable_cache else "DISABLED"
        self.logger.info(f"🚀 Replica initialized")
        self.logger.info(
            f"📊 Config: {self.num_replicas} replicas ({self.replica_cpu_per_task} CPU each), "
            f"{self.worker_pool_size} workers ({settings.WORKER_CPU_PER_TASK} CPU each)"
        )
        self.logger.info(
            f"🎯 REPL Cache: {cache_status} (max {self.max_cached_envs} envs/worker, "
            f"max {self.max_env_reuse_count} reuses/env)"
        )
        if self.enable_cache:
            self.logger.info(
                f"   💡 Cache-aware routing: each header → 1 primary worker + overflow when overloaded"
            )
            self.logger.info(
                f"   ⚖️  Overflow threshold: {self.overflow_threshold} tasks/worker (configurable per request)"
            )
            self.logger.info(
                f"   🔄 Auto-refresh: environments are refreshed after {self.max_env_reuse_count} reuses"
            )
        self.logger.info(
            f"📊 Resources: {available_cpus} CPUs, {available_memory:.1f}GB RAM, "
            f"{settings.REPL_MEMORY_LIMIT_GB}GB/task"
        )

        # Lazy initialization of workers
        self.workers = None
        
        # Task tracking for health monitoring (global shared Ray actor)
        from lean_verifier.taskcounter import get_or_create_global_task_counter
        self.task_counter = get_or_create_global_task_counter()
    
    def _get_workers(self):
        """Get globally shared cached workers"""
        if self.workers is None:
            self.workers = get_or_create_global_workers(
                self.worker_pool_size,
                self.enable_cache,
                self.max_cached_envs,
                self.max_env_reuse_count
            )
        return self.workers
    
    def _get_worker_for_code(self, code: str):
        """
        Select worker based on header hash for cache affinity.
        Ensures same imports always go to same worker -> higher cache hit rate!
        
        Args:
            code: Lean code string
            
        Returns:
            Selected worker actor
        """
        workers = self._get_workers()
        header_hash = extract_code_header_hash(code)
        # Use consistent hashing: same header -> same worker
        worker_idx = hash(header_hash) % len(workers)
        return workers[worker_idx]
    
    @app.get("/")
    async def root(self):
        """Root endpoint"""
        return {
            "message": "Lean Verifier Server (Ray Native + REPL Caching)", 
            "status": "running",
            "version": "3.0.0",
            "num_workers": self.worker_pool_size,
            "num_replicas": self.num_replicas,
            "replica_cpu_per_task": self.replica_cpu_per_task,
            "cache_enabled": self.enable_cache,
            "max_cached_envs": self.max_cached_envs,
            "max_env_reuse_count": self.max_env_reuse_count,
            "overflow_threshold": self.overflow_threshold
        }
    
    @app.get("/cache/stats")
    async def get_cache_stats(self):
        """Get REPL cache statistics from all workers"""
        try:
            workers = self._get_workers()
            
            # Get stats from all workers
            stats_futures = [worker.get_cache_stats.remote() for worker in workers]
            worker_stats = ray.get(stats_futures)
            
            # Calculate aggregate statistics
            total_hits = sum(s.get('cache_hits', 0) for s in worker_stats if 'cache_hits' in s)
            total_misses = sum(s.get('cache_misses', 0) for s in worker_stats if 'cache_misses' in s)
            total_verifications = sum(s.get('verification_count', 0) for s in worker_stats)
            total_requests = total_hits + total_misses
            overall_hit_rate = (total_hits / total_requests * 100) if total_requests > 0 else 0
            
            aggregate = {
                "enabled": self.enable_cache,
                "total_cache_hits": total_hits,
                "total_cache_misses": total_misses,
                "overall_hit_rate": f"{overall_hit_rate:.1f}%",
                "total_verifications": total_verifications,
                "num_workers": len(workers),
                "max_cached_envs_per_worker": self.max_cached_envs
            }
            
            return CacheStatsResponse(
                workers=worker_stats,
                aggregate=aggregate
            )
            
        except Exception as e:
            self.logger.error(f"❌ Failed to get cache stats: {e}")
            return {"error": str(e)}
    
    @app.post("/cache/clear")
    async def clear_cache(self):
        """Clear REPL environment caches in all workers"""
        try:
            workers = self._get_workers()
            
            self.logger.info(f"🗑️  Clearing cache in {len(workers)} workers")
            clear_futures = [worker.clear_cache.remote() for worker in workers]
            ray.get(clear_futures)
            
            self.logger.info("✅ Cache cleared in all workers")
            return {"status": "success", "workers_cleared": len(workers)}
            
        except Exception as e:
            self.logger.error(f"❌ Failed to clear cache: {e}")
            return {"status": "error", "message": str(e)}
            
    
    @app.post("/verify")
    async def verify_single(self, request: VerifyRequest):
        """Verify single code using intelligent worker routing"""
        start_time = time.time()
        self.logger.info(f"📝 Single verification request")
        
        try:
            # Use intelligent routing: same imports -> same worker -> cache hit!
            worker = self._get_worker_for_code(request.code)
            response = ray.get(
                worker.verify_single.remote(
                    request.code, request.timeout, request.max_retries
                )
            )
            self.logger.info(f"✅ Completed in {time.time() - start_time:.2f}s")
            
            # Parse results using utils functions
            parsed_result = parse_verification_results([response])[0]
            error_message = parse_verification_error_results([response])[0]
            
            return VerificationResult(
                problem=request.code,
                is_valid_no_sorry=parsed_result.get('is_valid_no_sorry', False),
                is_valid_with_sorry=parsed_result.get('is_valid_with_sorry', False),
                error_message=error_message,
                response=response
            )
            
        except Exception as e:
            self.logger.error(f"❌ Verification failed: {e}")
            return VerificationResult(
                problem=request.code,
                is_valid_no_sorry=False,
                is_valid_with_sorry=False,
                error_message=str(e),
                response=None
            )
    
    @app.post("/verify/batch")
    async def verify_batch(self, request: BatchVerifyRequest):
        """Batch verification with REPL caching and dynamic load balancing"""
        num_tasks = len(request.codes)
        self.logger.info(f"📦 Batch request: {num_tasks} tasks (cache: {self.enable_cache})")
        
        # Update total tasks counter
        self.task_counter.add_tasks.remote(num_tasks)
        
        start_time = time.time()
        
        # Start resource monitoring
        resource_monitor = ResourceMonitor(interval=0.5)
        resource_monitor.start()
        
        try:
            result = await self._verify_batch_ray_native(request, start_time)
            
            # Stop resource monitoring
            resource_stats = resource_monitor.stop()
            
            # Add resource statistics
            result.cpu_stats = {
                'num_samples': resource_stats['samples'],
                'duration_seconds': round(resource_stats['duration'], 2),
                'has_real_cpu_data': resource_stats['has_real_cpu_data']
            }
            
            # Real CPU usage (actual system CPU)
            if resource_stats['has_real_cpu_data']:
                result.cpu_stats['avg_cpu_percent'] = round(resource_stats.get('avg_cpu_real', 0), 2)
                result.cpu_stats['max_cpu_percent'] = round(resource_stats.get('max_cpu_real', 0), 2)
                result.cpu_stats['min_cpu_percent'] = round(resource_stats.get('min_cpu_real', 0), 2)
                
                # Memory stats
                if 'avg_memory_percent' in resource_stats:
                    result.cpu_stats['avg_memory_percent'] = round(resource_stats['avg_memory_percent'], 2)
                    result.cpu_stats['max_memory_percent'] = round(resource_stats['max_memory_percent'], 2)
            else:
                # Fallback to Ray reserved (less accurate)
                result.cpu_stats['avg_cpu_percent'] = round(resource_stats.get('avg_ray_reserved_percent', 0), 2)
                result.cpu_stats['max_cpu_percent'] = round(resource_stats.get('max_ray_reserved_percent', 0), 2)
                result.cpu_stats['min_cpu_percent'] = round(resource_stats.get('min_ray_reserved_percent', 0), 2)
                result.cpu_stats['warning'] = 'psutil not available, showing Ray reserved CPU (not actual usage)'
            
            # Ray resource allocation (for reference)
            result.cpu_stats['ray_reserved_percent'] = {
                'avg': round(resource_stats.get('avg_ray_reserved_percent', 0), 2),
                'max': round(resource_stats.get('max_ray_reserved_percent', 0), 2),
            }
            
            # Get cache statistics if enabled
            if self.enable_cache:
                try:
                    workers = self._get_workers()
                    stats_futures = [worker.get_cache_stats.remote() for worker in workers]
                    worker_stats = ray.get(stats_futures)
                    
                    total_hits = sum(s.get('cache_hits', 0) for s in worker_stats if 'cache_hits' in s)
                    total_misses = sum(s.get('cache_misses', 0) for s in worker_stats if 'cache_misses' in s)
                    total_requests = total_hits + total_misses
                    hit_rate = (total_hits / total_requests * 100) if total_requests > 0 else 0
                    
                    result.cache_stats = {
                        "enabled": True,
                        "total_hits": total_hits,
                        "total_misses": total_misses,
                        "hit_rate": f"{hit_rate:.1f}%",
                        "total_requests": total_requests
                    }
                except Exception as e:
                    self.logger.warning(f"Failed to get cache stats: {e}")
                    result.cache_stats = {"error": str(e)}
            else:
                result.cache_stats = {"enabled": False}
            
            # Add throughput and config
            total_time = time.time() - start_time
            result.throughput = num_tasks / total_time if total_time > 0 else 0.0
            
            result.config = {
                "num_workers": len(self._get_workers()),
                "num_replicas": self.num_replicas,
                "cache_enabled": self.enable_cache,
                "max_cached_envs": self.max_cached_envs,
                "overflow_threshold": request.overflow_threshold if request.overflow_threshold is not None else self.overflow_threshold,
                "routing_strategy": "cache-aware with overflow"
            }
            
            # Log resource usage
            if resource_stats['has_real_cpu_data']:
                self.logger.info(
                    f"📊 CPU (real): avg={resource_stats.get('avg_cpu_real', 0):.1f}%, "
                    f"max={resource_stats.get('max_cpu_real', 0):.1f}%"
                )
                if 'avg_memory_percent' in resource_stats:
                    self.logger.info(
                        f"💾 Memory: avg={resource_stats['avg_memory_percent']:.1f}%, "
                        f"max={resource_stats['max_memory_percent']:.1f}%"
                    )
            else:
                self.logger.info(
                    f"📊 Ray reserved: avg={resource_stats.get('avg_ray_reserved_percent', 0):.1f}%, "
                    f"max={resource_stats.get('max_ray_reserved_percent', 0):.1f}% "
                    f"(install psutil for real CPU usage)"
                )
            
            if self.enable_cache and result.cache_stats.get('enabled') and not result.cache_stats.get('error'):
                hit_rate = result.cache_stats.get('hit_rate', '0.0%')
                self.logger.info(f"🎯 Cache: {hit_rate} hit rate")
            
            # All tasks completed, no need to update counter
            # Each task completion already decremented the counter
            
            return result
                
        except Exception as e:
            resource_monitor.stop()
            self.logger.error(f"❌ Batch verification failed: {e}")
            import traceback
            self.logger.error(traceback.format_exc())

            # Reset tasks on failure
            self.task_counter.remove_tasks.remote(num_tasks)
            
            return BatchVerificationResponse(
                results=[],
                total=0,
                pass_rate_no_sorry=0.0,
                pass_rate_with_sorry=0.0,
                processing_time=time.time() - start_time,
                throughput=0.0,
                cpu_stats=None,
                cache_stats=None,
                config=None
            )
    
    def _sort_tasks_by_complexity(self, codes: List[str]) -> List[Tuple[int, str, float]]:
        """Sort tasks by complexity (descending) to avoid long-tail effects
        
        Returns:
            List of (original_index, code, complexity) tuples, sorted by complexity desc
        """
        task_complexities = []
        for idx, code in enumerate(codes):
            complexity = estimate_task_complexity(code)
            task_complexities.append((idx, code, complexity))
        
        # Sort by complexity descending (complex tasks first)
        task_complexities.sort(key=lambda x: x[2], reverse=True)
        
        complexity_stats = [tc[2] for tc in task_complexities]
        avg_complexity = sum(complexity_stats) / len(complexity_stats) if complexity_stats else 0
        max_complexity = max(complexity_stats) if complexity_stats else 0
        min_complexity = min(complexity_stats) if complexity_stats else 0
        self.logger.info(
            f"📊 Task complexity: avg={avg_complexity:.1f}, max={max_complexity:.1f}, min={min_complexity:.1f}"
        )
        
        return task_complexities
    
    def _select_worker_for_task(
        self,
        code: str,
        header_hash: str,
        workers: List,
        worker_active_counts: List[int],
        overflow_threshold: int
    ) -> Tuple[int, bool, bool]:
        """Select best worker with cache-aware + secondary affinity + load balancing
        
        Returns:
            (worker_idx, is_overflow, used_secondary_affinity)
        """
        primary_worker_idx = hash(header_hash) % len(workers)
        
        # Check if primary worker is overloaded
        if worker_active_counts[primary_worker_idx] < overflow_threshold:
            return primary_worker_idx, False, False
        
        # Primary overloaded, use secondary cache affinity
        # Strategy: Among least loaded workers, pick the one with closest hash
        
        # Find top-K least loaded workers (K=3 for balance between performance and cache)
        K = min(3, len(workers))
        candidate_indices = sorted(
            range(len(workers)), 
            key=lambda idx: worker_active_counts[idx]
        )[:K]
        
        if len(candidate_indices) == 1:
            return candidate_indices[0], True, False
        
        # Among candidates, select the one with closest hash (secondary cache affinity)
        primary_hash_value = hash(header_hash)
        best_worker = min(
            candidate_indices,
            key=lambda idx: abs(primary_hash_value - idx * 1000000)  # Hash distance proxy
        )
        
        return best_worker, True, True
    
    @staticmethod
    def _get_adaptive_batch_size(remaining: int) -> int:
        """Calculate adaptive batch collection size based on remaining tasks"""
        if remaining > 100:
            return max(1, remaining // 20)  # 5% for large batches
        elif remaining > 20:
            return max(1, remaining // 10)  # 10% for medium batches
        else:
            return min(remaining, 5)  # Small fixed size for small batches
    
    async def _verify_batch_ray_native(
        self, 
        request: BatchVerifyRequest, 
        start_time: float
    ) -> BatchVerificationResponse:
        """Ray native task scheduling with dynamic load balancing and optimizations
        
        Optimizations:
        1. Task complexity sorting: Complex tasks submitted first (avoid long-tail effects)
        2. Dynamic streaming submission: Stream tasks based on worker availability
        3. Secondary cache affinity: Overflow to hash-similar workers
        4. Adaptive batch collection: Dynamic num_returns based on task scale
        """
        codes = request.codes
        timeout = request.timeout
        
        workers = self._get_workers()
        
        self.logger.info(f"🚀 Submitting {len(codes)} tasks to {len(workers)} cached workers (optimized scheduling)")
        
        loop = asyncio.get_event_loop()
        
        def run_ray_tasks_optimized():
            """Optimized intelligent routing with dynamic load balancing"""
            results = [None] * len(codes)
            completed_count = 0
            progress_interval = max(1, len(codes) // 10)
            
            # ========== Optimization 1: Task Complexity Sorting ==========
            task_complexities = self._sort_tasks_by_complexity(codes)
            
            # ========== Optimization 2: Dynamic Streaming Submission ==========
            # Instead of submitting all tasks at once, stream them dynamically
            # This allows better load balancing based on actual worker availability
            
            # Overflow threshold configuration
            min_threshold = request.overflow_threshold if request.overflow_threshold is not None else self.overflow_threshold
            overflow_threshold = max(len(codes) // len(workers), min_threshold)
            
            # Track real-time worker load (submitted - completed)
            worker_active_counts = [0] * len(workers)  # Real-time active tasks per worker
            worker_submitted_counts = [0] * len(workers)  # Total submitted per worker
            
            # Streaming window: submit N*workers tasks initially, then submit as tasks complete
            initial_window_size = min(len(codes), overflow_threshold * len(workers))
            
            task_to_info = {}  # task_ref -> (code_idx, worker_idx)
            pending_tasks = task_complexities.copy()  # Tasks not yet submitted
            overflow_count = 0
            secondary_affinity_count = 0
            
            # Phase 1: Submit initial window
            initial_submit_count = min(initial_window_size, len(pending_tasks))
            for _ in range(initial_submit_count):
                code_idx, code, _ = pending_tasks.pop(0)
                header_hash = extract_code_header_hash(code)
                worker_idx, is_overflow, used_secondary = self._select_worker_for_task(
                    code, header_hash, workers, worker_active_counts, overflow_threshold
                )
                if is_overflow:
                    overflow_count += 1
                if used_secondary:
                    secondary_affinity_count += 1
                
                task = workers[worker_idx].verify_single.remote(
                    code, timeout, request.max_retries
                )
                task_to_info[task] = (code_idx, worker_idx)
                worker_active_counts[worker_idx] += 1
                worker_submitted_counts[worker_idx] += 1
            
            self.logger.info(
                f"🎯 Initial submission: {initial_submit_count}/{len(codes)} tasks "
                f"(window_size={overflow_threshold}*{len(workers)})"
            )
            
            # Phase 2: Stream remaining tasks as workers complete
            active_tasks = list(task_to_info.keys())
            
            while active_tasks:
                batch_size = self._get_adaptive_batch_size(len(active_tasks))
                
                # Wait for some tasks to complete
                ready_tasks, active_tasks = ray.wait(
                    active_tasks,
                    num_returns=min(len(active_tasks), batch_size),
                    timeout=None
                )
                
                # Process completed tasks
                for task in ready_tasks:
                    code_idx, worker_idx = task_to_info[task]
                    results[code_idx] = ray.get(task)
                    completed_count += 1
                    
                    # Update real-time worker load
                    worker_active_counts[worker_idx] -= 1
                    
                    # Update task counter (task completed)
                    self.task_counter.remove_tasks.remote(1)
                    
                    # Submit new task to the now-available worker (if any pending)
                    if pending_tasks:
                        new_code_idx, new_code, _ = pending_tasks.pop(0)
                        new_header_hash = extract_code_header_hash(new_code)
                        new_worker_idx, is_overflow, used_secondary = self._select_worker_for_task(
                            new_code, new_header_hash, workers, worker_active_counts, overflow_threshold
                        )
                        if is_overflow:
                            overflow_count += 1
                        if used_secondary:
                            secondary_affinity_count += 1
                        
                        new_task = workers[new_worker_idx].verify_single.remote(
                            new_code, timeout, request.max_retries
                        )
                        task_to_info[new_task] = (new_code_idx, new_worker_idx)
                        worker_active_counts[new_worker_idx] += 1
                        worker_submitted_counts[new_worker_idx] += 1
                        active_tasks.append(new_task)
                    
                    # Progress logging
                    if completed_count % progress_interval == 0 or completed_count == len(codes):
                        elapsed = time.time() - start_time
                        rate = completed_count / elapsed if elapsed > 0 else 0
                        
                        # Calculate Ray resource allocation (not real CPU usage)
                        try:
                            total_cpu = ray.cluster_resources().get("CPU", 0)
                            available_cpu = ray.available_resources().get("CPU", 0)
                            ray_reserved_percent = ((total_cpu - available_cpu) / total_cpu * 100) if total_cpu > 0 else 0
                        except Exception:
                            ray_reserved_percent = 0
                        
                        # Real-time load stats
                        current_max_load = max(worker_active_counts) if worker_active_counts else 0
                        current_avg_load = sum(worker_active_counts) / len(worker_active_counts) if worker_active_counts else 0
                        
                        self.logger.info(
                            f"⏳ Progress: {completed_count}/{len(codes)} "
                            f"({completed_count/len(codes)*100:.1f}%) "
                            f"| {elapsed:.1f}s | {rate:.1f} tasks/s "
                            f"| Load: avg={current_avg_load:.1f}, max={current_max_load} "
                            f"| Reserved: {ray_reserved_percent:.1f}%"
                        )
            
            # Log final routing statistics
            max_tasks = max(worker_submitted_counts) if worker_submitted_counts else 0
            min_tasks = min(worker_submitted_counts) if worker_submitted_counts else 0
            avg_tasks = sum(worker_submitted_counts) / len(worker_submitted_counts) if worker_submitted_counts else 0
            active_workers = sum(1 for count in worker_submitted_counts if count > 0)
            self.logger.info(
                f"✅ Final routing stats: {len(codes)} tasks → {active_workers}/{len(workers)} workers "
                f"(avg={avg_tasks:.1f}, min={min_tasks}, max={max_tasks})"
            )
            self.logger.info(
                f"🎯 Cache strategy: {overflow_count} overflows ({overflow_count/len(codes)*100:.1f}%), "
                f"{secondary_affinity_count} used secondary affinity ({secondary_affinity_count/len(codes)*100:.1f}%)"
            )
            
            return results
        
        # Execute in thread pool
        all_responses = await loop.run_in_executor(None, run_ray_tasks_optimized)
        
        total_time = time.time() - start_time
        self.logger.info(f"✅ Completed {len(all_responses)} tasks in {total_time:.2f}s")
        
        # Parse results using utils functions
        verification_results = []
        if all_responses:
            parsed_results = parse_verification_results(all_responses)
            error_feedbacks = parse_verification_error_results(all_responses)
            
            for problem, response, parsed_result, error_feedback in zip(
                codes, all_responses, parsed_results, error_feedbacks
            ):
                verification_results.append(VerificationResult(
                    problem=problem,
                    is_valid_no_sorry=parsed_result.get('is_valid_no_sorry', False),
                    is_valid_with_sorry=parsed_result.get('is_valid_with_sorry', False),
                    error_message=error_feedback,
                    response=response
                ))
        
        # Calculate pass rates
        pass_count_no_sorry = sum(1 for r in verification_results if r.is_valid_no_sorry)
        pass_count_with_sorry = sum(1 for r in verification_results if r.is_valid_with_sorry)
        pass_rate_no_sorry = pass_count_no_sorry / len(verification_results) if verification_results else 0.0
        pass_rate_with_sorry = pass_count_with_sorry / len(verification_results) if verification_results else 0.0
        
        self.logger.info(
            f"📊 Pass rates: no_sorry={pass_rate_no_sorry:.2%}, "
            f"with_sorry={pass_rate_with_sorry:.2%}"
        )
        
        return BatchVerificationResponse(
            results=verification_results,
            total=len(verification_results),
            pass_rate_no_sorry=pass_rate_no_sorry,
            pass_rate_with_sorry=pass_rate_with_sorry,
            processing_time=total_time,
            throughput=len(verification_results) / total_time if total_time > 0 else 0.0
        )