"""
Standalone health check service.

Uses a dedicated replica so verification work cannot block health checks.
"""

import time
from typing import Dict, Any, Optional

import ray
from ray import serve
from fastapi import FastAPI
from pydantic import BaseModel, Field

from lean_verifier.config import settings


class HealthResponse(BaseModel):
    """Health check response"""
    status: str = Field(description="Service status")
    timestamp: float = Field(description="Timestamp")
    ray_status: str = Field(description="Ray cluster status")
    num_workers: int = Field(description="Number of workers")
    num_replicas: int = Field(description="Number of replicas")
    cache_enabled: bool = Field(description="Whether REPL caching is enabled")


class TaskStatusResponse(BaseModel):
    """Task status response"""
    success: bool = Field(description="Whether the status query was successful")
    total_tasks: int = Field(description="Total tasks (pending + active)")
    timestamp: float = Field(description="Timestamp")
    error: Optional[str] = Field(default=None, description="Error message if query failed")


class StatResponse(BaseModel):
    """Combined statistics response"""
    success: bool = Field(description="Whether the query was successful")
    timestamp: float = Field(description="Timestamp")
    total_tasks: int = Field(description="Total tasks")
    ray_stats: Optional[Dict[str, Any]] = Field(default=None, description="Ray cluster statistics")
    error: Optional[str] = Field(default=None, description="Error message if query failed")


# FastAPI app for health check service
health_app = FastAPI(
    title="Lean Verifier Health Check Service",
    description="Dedicated health check service (isolated from verification tasks)",
    version="1.0.0",
    redirect_slashes=False  # Disable auto-redirect so /health and /health/ both work
)


@serve.deployment(
    num_replicas=1,  # Single health-check replica for health endpoints only
    ray_actor_options={"num_cpus": 0.1}  # Minimal CPU
)
@serve.ingress(health_app)
class HealthCheckService:
    """Standalone health service — separate replica, unaffected by verification load."""
    
    def __init__(self):
        # Load from settings
        self.worker_pool_size = settings.WORKER_POOL_SIZE
        self.num_replicas = settings.SERVE_NUM_REPLICAS
        self.enable_cache = settings.ENABLE_REPL_CACHE
        
        # Cached worker list (read-only, no initialization)
        self._workers = None
    
    def _get_workers(self):
        """Return existing workers (read-only, does not create workers)."""
        if self._workers is None:
            workers = []
            for i in range(self.worker_pool_size):
                worker_name = f"lean_worker_{i}"
                try:
                    worker = ray.get_actor(worker_name)
                    workers.append(worker)
                except ValueError:
                    # Worker missing, skip
                    continue
            self._workers = workers
        return self._workers
    
    @health_app.get("/init")
    async def health(self):
        """Lightweight health endpoint — does not depend on worker initialization.
        """
        try:
            ray_status = "connected" if ray.is_initialized() else "disconnected"
            
            # Fast path — do not wait on workers
            return HealthResponse(
                status="healthy",
                timestamp=time.time(),
                ray_status=ray_status,
                num_workers=self.worker_pool_size,
                num_replicas=self.num_replicas,
                cache_enabled=self.enable_cache
            )
        except Exception as e:
            # Health check failed
            return HealthResponse(
                status="unhealthy",
                timestamp=time.time(),
                ray_status="error",
                num_workers=0,
                num_replicas=0,
                cache_enabled=False
            )
    
    @health_app.get("/stats")
    async def stat(self):
        """Aggregate stats — task state and Ray cluster metrics."""
        total_tasks = 0
        ray_stats = None
        success = False
        error_msg = None
        
        try:
            # 1. Task status
            try:
                from lean_verifier.taskcounter import get_or_create_global_task_counter
                counter = get_or_create_global_task_counter()
                status_future = counter.get_status.remote()
                status = await status_future
                total_tasks = status.get("total_tasks", 0)
            except Exception as e:
                error_msg = f"Failed to get task status: {str(e)}"
            
            # 2. Ray cluster stats
            try:
                cluster_resources = ray.cluster_resources()
                available_resources = ray.available_resources()
                
                ray_stats = {
                    "cluster": {},
                    "usage": {},
                    "workers": {}
                }
                
                # Cluster resource overview
                for resource, total in cluster_resources.items():
                    available = available_resources.get(resource, 0)
                    used = total - available
                    ray_stats["cluster"][resource] = {
                        "total": total,
                        "available": available,
                        "used": used,
                        "utilization_percent": round((used / total * 100), 2) if total > 0 else 0
                    }
                
                # CPU and memory specifics
                if "CPU" in cluster_resources:
                    cpu_info = ray_stats["cluster"]["CPU"]
                    ray_stats["usage"]["cpu_cores_used"] = cpu_info["used"]
                    ray_stats["usage"]["cpu_utilization"] = cpu_info["utilization_percent"]
                
                if "memory" in cluster_resources:
                    mem_info = ray_stats["cluster"]["memory"]
                    ray_stats["usage"]["memory_gb_used"] = round(mem_info["used"] / (1024**3), 2)
                    ray_stats["usage"]["memory_utilization"] = mem_info["utilization_percent"]
                
                # Workers info
                ray_stats["workers"]["num_replicas"] = self.num_replicas
                ray_stats["workers"]["worker_pool_size"] = self.worker_pool_size
                ray_stats["workers"]["cache_enabled"] = self.enable_cache
                ray_stats["workers"]["max_cached_envs"] = settings.MAX_CACHED_ENVS
                ray_stats["workers"]["max_env_reuse_count"] = settings.MAX_ENV_REUSE_COUNT
                
                # Nodes info
                try:
                    nodes = ray.nodes()
                    ray_stats["nodes"] = {
                        "total_nodes": len(nodes),
                        "alive_nodes": len([n for n in nodes if n['Alive']]),
                    }
                except:
                    ray_stats["nodes"] = {"error": "Unable to fetch node info"}
                
            except Exception as e:
                if not error_msg:
                    error_msg = f"Failed to get Ray stats: {str(e)}"
                ray_stats = {"error": str(e)}
            
            # Success if at least one part succeeded
            success = error_msg is None or ray_stats is not None
        
        except Exception as e:
            # Outer handler
            error_msg = f"Unexpected error: {str(e)}"
            success = False
        
        return StatResponse(
            success=success,
            total_tasks=total_tasks,
            ray_stats=ray_stats,
            timestamp=time.time(),
            error=error_msg
        )
