import os
from importlib import resources
from pathlib import Path

from pydantic import Field, ValidationError, field_validator
from pydantic_settings import BaseSettings, SettingsConfigDict


class Settings(BaseSettings):
    """Lean Verifier Server Configuration
    
    All settings can be configured via environment variables with LEANSERVER_ prefix.
    Example: LEANSERVER_HOST=localhost LEANSERVER_PORT=8080
    """
    
    # Server configuration
    HOST: str = Field("0.0.0.0", description="Server bind address")
    PORT: int = Field(8000, description="Server port")
    
    # Logging configuration
    LOG_DIR: str = Field("./logs", description="Log directory path")
    LOG_LEVEL: str = Field("INFO", description="Logging level (DEBUG/INFO/WARNING/ERROR)")
    
    # Workspace configuration
    WORKSPACE: str = Field(
        default_factory=lambda: str(Path(resources.files("lean_verifier")).parent),
        description="Lean workspace directory"
    )
    
    # REPL configuration
    MAX_REPLS: int = Field(os.cpu_count() or 1, description="Maximum number of REPL processes")
    REPL_MEMORY_LIMIT_GB: int = Field(8, description="Memory limit per REPL process (GB)")
    REPL_MEMORY_RATIO: float = Field(0.95, description="Memory usage ratio threshold")
    HARD_ENFORCE_MEMORY_LIMIT: bool = Field(False, description="Strictly enforce memory limits")
    
    # Ray Serve configuration
    SERVE_NUM_REPLICAS: int = Field(32, description="Number of Ray Serve replicas for HTTP handling")
    REPLICA_CPU_PER_TASK: float = Field(
        1.0,
        description="CPU resources per replica (0.5=half core, 0.25=quarter core). Each replica handles HTTP requests"
    )
    WORKER_POOL_SIZE: int = Field(320, description="Global worker pool size for REPL processing")
    WORKER_CPU_PER_TASK: float = Field(
        1.0, 
        description="CPU resources per worker (0.5=half core). Max workers = available_cpus / this value"
    )
    
    # REPL Cache configuration
    ENABLE_REPL_CACHE: bool = Field(True, description="Enable REPL environment caching")
    MAX_CACHED_ENVS: int = Field(
        3,
        description="Max cached environments per worker (3 is optimal with intelligent routing)"
    )
    MAX_ENV_REUSE_COUNT: int = Field(
        12,
        description="Max reuse count per cached environment before refresh (prevents memory leaks)"
    )
    OVERFLOW_THRESHOLD: int = Field(
        5,
        description="Min tasks per worker before overflow (actual threshold = max(avg_load, this value))"
    )

    model_config = SettingsConfigDict(
        env_file=".env", env_file_encoding="utf-8", env_prefix="LEANSERVER_"
    )
    
    @field_validator("HOST", mode="before")
    @classmethod
    def validate_host(cls, v):
        if not v or v == "":
            return "0.0.0.0"
        return v
    
    @field_validator("PORT", mode="before")
    @classmethod
    def validate_port(cls, v):
        if not v or v == "":
            return 8000
        return v

    @field_validator("WORKSPACE", mode="before")
    @classmethod
    def validate_workspace(cls, v):
        if v == "":
            return str(Path(resources.files("lean_verifier")).parent)
        return v

    @field_validator("MAX_REPLS", mode="before")
    @classmethod
    def validate_max_repls(cls, v):
        if not v or v == "":
            return os.cpu_count() or 1
        return v

    @field_validator("REPL_MEMORY_LIMIT_GB", mode="before")
    @classmethod
    def validate_repl_memory_limit_gb(cls, v):
        if v == "":
            return None
        return v
    
    @field_validator("REPL_MEMORY_RATIO", mode="before")
    @classmethod
    def validate_repl_memory_ratio(cls, v):
        if v == "":
            return 0.95
        return v

    @field_validator("HARD_ENFORCE_MEMORY_LIMIT", mode="before")
    @classmethod
    def validate_hard_enforce_memory_limit(cls, v):
        if not v or v == "":
            return False
        return v
    
    @field_validator("SERVE_NUM_REPLICAS", mode="before")
    @classmethod
    def validate_serve_num_replicas(cls, v):
        if not v or v == "":
            return 4
        return v
    
    @field_validator("REPLICA_CPU_PER_TASK", mode="before")
    @classmethod
    def validate_replica_cpu_per_task(cls, v):
        if not v or v == "":
            return 1.0
        return float(v)
    
    @field_validator("WORKER_POOL_SIZE", mode="before")
    @classmethod
    def validate_worker_pool_size(cls, v):
        if not v or v == "":
            return 32
        return v
    
    @field_validator("WORKER_CPU_PER_TASK", mode="before")
    @classmethod
    def validate_worker_cpu_per_task(cls, v):
        if not v or v == "":
            return 1.0
        return v
    
try:
    settings = Settings()
except ValidationError as e:
    missing_vars = [
        f"LEANSERVER_{str(err['loc'][0]).upper()}"
        for err in e.errors()
        if err["type"] == "missing"
    ]
    raise ValueError(f"Missing environment variables: {', '.join(missing_vars)}")