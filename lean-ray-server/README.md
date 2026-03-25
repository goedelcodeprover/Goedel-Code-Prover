# Lean Verifier Server

Lean code verification server based on Ray Serve with real-time task processing support.

## Features

- 🚀 **High Performance**: Distributed processing with Ray Serve (25+ workers)
- 💾 **Intelligent Caching**: REPL environment caching with 90%+ hit rate
- 🎯 **Smart Routing**: Header-hash based routing for optimal cache affinity
- ⚖️ **Dynamic Load Balancing**: Automatic overflow to prevent worker bottlenecks
- 🔄 **Real-time Processing**: Single and batch code verification with concurrent execution
- 🛡️ **Error Handling**: Comprehensive error handling with automatic retries
- 📈 **Rich Monitoring**: Cache statistics, CPU metrics, and performance tracking
- 🔧 **Configurable**: Flexible resource and caching configuration per request

## Installation

```bash
pip install ray[serve] fastapi uvicorn pydantic loguru tqdm
```

Or install from requirements:
```bash
pip install -r requirements.txt
```

## Quick Start

### 1. Start Ray Cluster (Required)

**⚠️ Important: Ray cluster must be started first before running the server.**

```bash
# Start Ray cluster with default settings
ray start --head --port=6379

# Start Ray cluster with specific resources
ray start --head --port=6379 --num-cpus=8 --memory=32000000000

# Or set RAY_ADDRESS environment variable
export RAY_ADDRESS=ray://<head-node-ip>:10001
```

### 2. Start Server

#### Using shell script (recommended)
```bash
./start_server.sh
./start_server.sh --workers 8
```

#### Using Python directly
```bash
# Ray Serve mode (recommended)
python lean_verifier/start_server.py --mode serve --workers 8

# FastAPI mode
python lean_verifier/start_server.py --mode fastapi --port 8000
```

### 3. Test Server

```bash
# Health check
curl http://localhost:8000/health

# Single verification
curl -X POST http://localhost:8000/verify \
  -H "Content-Type: application/json" \
  -d '{"code": "def hello : String := \"Hello, Lean!\"", "timeout": 60}'

# Batch verification
curl -X POST http://localhost:8000/verify/batch \
  -H "Content-Type: application/json" \
  -d '{"codes": ["def add (a b : Nat) : Nat := a + b", "def mul (a b : Nat) : Nat := a * b"], "timeout": 60}'
```

### 3. Run Tests

```bash
# Run all tests
python test/test_server.py

# Run specific test
python test/test_server.py --test replica --concurrent 8
python test/test_server.py --test smart-split
```

## API Endpoints

### Health Check
- **GET** `/health` - Get server status and resource info
  - Returns: `status`, `workers`, `cache_enabled`

### Verification Endpoints
- **POST** `/verify` - Single code verification
  - Body: `{"code": "...", "timeout": 60, "max_retries": 2}`
- **POST** `/verify/batch` - Batch code verification with intelligent routing
  - Body: `{"codes": [...], "timeout": 60, "max_retries": 2, "max_tasks_per_worker": 10}`
  - `max_tasks_per_worker`: Optional load balancing parameter (default: 10)
  - Returns: results with cache stats, CPU metrics, and config

### Cache Management
- **GET** `/cache/stats` - Get cache statistics from all workers
  - Returns: per-worker stats and aggregate metrics
- **POST** `/cache/clear` - Clear all cached REPL environments

## Configuration

### Environment Variables (.env)

Copy `.env.template` to `.env` and customize:

```bash
cp .env.template .env
```

Configuration options:
- `LEANSERVER_HOST` - Server host (default: 0.0.0.0)
- `LEANSERVER_PORT` - Server port (default: 8000)
- `LEANSERVER_SERVE_NUM_REPLICAS` - Number of replicas (default: 4)
- `LEANSERVER_LOG_LEVEL` - Log level (default: INFO)
- See `.env.template` for all options

### Command Line Arguments

```bash
python lean_verifier/start_server.py --help
```

Main arguments:
- `--host`: Server host address (default: from .env or 0.0.0.0)
- `--port`: Server port (default: from .env or 8000)
- `--workers`: Number of replicas (default: from .env or 4)
- `--cpus`: Ray CPU count
- `--memory`: Ray memory limit (GB)
- `--log-level`: Log level
- `--mode`: Run mode (serve/fastapi)

Priority: **command line args > .env file > defaults**

## Architecture

### System Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    Ray Serve (Port 8000)                     │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│  │Replica 1 │  │Replica 2 │  │Replica 3 │  │Replica 4 │   │  HTTP handlers
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘   │  (concurrent requests)
└───────┼─────────────┼─────────────┼─────────────┼──────────┘
        │             │             │             │
        └─────────────┴─────────────┴─────────────┘
                      │
        ┌─────────────┴─────────────────┐
        │  Global Shared Worker Pool    │
        │  ┌────────┐  ┌────────┐       │
        │  │Worker 1│  │Worker 2│  ...  │  Persistent REPL processes
        │  │(REPL + │  │(REPL + │       │  with environment caching
        │  │ Cache) │  │ Cache) │       │
        │  └────────┘  └────────┘       │
        └───────────────────────────────┘
```

### Key Features

1. **Multiple Replicas**: Handle concurrent HTTP requests (default: 4)
2. **Shared Worker Pool**: All replicas share same workers (default: 25-64)
3. **Persistent REPLs**: Each worker holds a long-running Lean process
4. **Environment Caching**: Cache imported modules per worker (90%+ hit rate)
5. **Intelligent Routing**: Same imports → same worker → cache hit
6. **Dynamic Load Balancing**: Overflow to other workers if primary overloaded

### Caching Strategy

```python
# Example: Two tasks with same imports
task1 = "import Mathlib\ndef add := 1"
task2 = "import Mathlib\ndef sub := 2"

# Both routed to Worker-5 (based on header hash)
# Worker-5 loads "import Mathlib" once → cached
# task1: Cache MISS (load imports) ~3.5s
# task2: Cache HIT (reuse env) ~0.05s ⚡
```

## Performance Optimization

### 1. Tuning Load Balancing

Adjust `max_tasks_per_worker` per request for different workloads:

```python
# High concurrency (distribute widely)
payload = {
    "codes": [...],
    "max_tasks_per_worker": 2  # Low limit → high distribution
}

# High cache hit (concentrate tasks)
payload = {
    "codes": [...],
    "max_tasks_per_worker": 20  # High limit → high cache affinity
}
```

### 2. Resource Configuration

Configure via environment variables in `start_server.sh`:

```bash
export WORKER_POOL_SIZE=64      # Number of workers (adjust to CPU cores)
export SERVE_NUM_REPLICAS=4     # HTTP replicas (4-8 is usually enough)
export MAX_CACHED_ENVS=10       # Cache size per worker
export MAX_ENV_REUSE_COUNT=100  # Max reuse count per env (auto-refresh to prevent memory leaks)
export MAX_TASKS_PER_WORKER=10  # Default load balancing threshold
```

**Cache Auto-Refresh**: Each cached environment is automatically refreshed after 100 reuses to prevent memory leaks or fragmentation. This ensures long-running servers remain stable.

### 3. Performance Metrics

Get real-time statistics:

```bash
# Cache statistics
curl http://localhost:8000/cache/stats

# Ray cluster statistics
curl http://localhost:8000/stats/ray
```

## Monitoring and Logs

### Log Files
- `logs/lean_verifier_server.log` - Server logs

### Health Check
```bash
curl http://localhost:8000/health
```

Returns:
- Service status
- Ray cluster status
- CPUs per replica
- Recommended batch size

## Troubleshooting

### 1. Dependency Issues
```bash
python lean_verifier/start_server.py --check-deps
```

### 2. Ray Cluster Issues
```bash
ray status
```

### 3. Resource Errors

If you see "Insufficient CPU/memory resources":
- Reduce `--workers` count
- Increase `--memory` parameter
- Adjust resource allocation

### 4. Port Conflicts
```bash
./start_server.sh --port 8001
```

## Development Guide

### Adding New API Endpoints

1. Add route in `server.py` using `@app.post()` or `@app.get()`
2. Add corresponding method in `LeanVerifierService` class
3. Update client code if needed

### Custom Verification Logic

1. Inherit from `LeanVerifier` class
2. Override verification methods
3. Use custom verifier in service

## License

MIT License