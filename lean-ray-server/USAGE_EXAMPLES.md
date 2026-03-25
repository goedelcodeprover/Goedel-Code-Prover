# Lean Verifier Server - Usage Examples

## Basic Usage

### 1. Single Code Verification

```python
import requests

response = requests.post(
    "http://localhost:8000/verify",
    json={
        "code": "def add (a b : Nat) : Nat := a + b",
        "timeout": 60
    }
)

result = response.json()
print(f"Valid: {result['is_valid_no_sorry']}")
```

### 2. Batch Verification

```python
import requests

codes = [
    "import Mathlib\ndef add (a b : Nat) : Nat := a + b",
    "import Mathlib\ndef sub (a b : Nat) : Nat := a - b",
    # ... more codes
]

response = requests.post(
    "http://localhost:8000/verify/batch",
    json={
        "codes": codes,
        "timeout": 60,
        "max_retries": 2
    }
)

data = response.json()
print(f"Pass rate: {data['pass_rate_no_sorry']:.2%}")
print(f"Throughput: {data['throughput']:.2f} codes/s")
print(f"Cache hit rate: {data['cache_stats']['hit_rate']}")
```

## Advanced Usage

### 3. Dynamic Load Balancing

Control task distribution per request:

```python
# Scenario 1: Many identical imports → concentrate for cache hits
response = requests.post(
    "http://localhost:8000/verify/batch",
    json={
        "codes": codes_with_same_imports,
        "max_tasks_per_worker": 50  # Allow high concentration
    }
)

# Scenario 2: Diverse imports → distribute for parallelism
response = requests.post(
    "http://localhost:8000/verify/batch",
    json={
        "codes": codes_with_different_imports,
        "max_tasks_per_worker": 2  # Force wide distribution
    }
)
```

### 4. Monitor Cache Performance

```python
import requests

# Get cache statistics
stats = requests.get("http://localhost:8000/cache/stats").json()

print(f"Overall hit rate: {stats['aggregate']['overall_hit_rate']}")
print(f"Total verifications: {stats['aggregate']['total_verifications']}")
print(f"Active workers: {stats['aggregate']['num_workers']}")

# Per-worker stats
for i, worker in enumerate(stats['workers'][:5]):  # First 5 workers
    print(f"Worker {i}: {worker['cache_hits']} hits, {worker['verification_count']} tasks")
```

### 5. Clear Cache When Needed

```python
import requests

# Clear all cached environments (e.g., after Lean version upgrade)
response = requests.post("http://localhost:8000/cache/clear")
print(response.json())  # {"status": "success", "workers_cleared": 25}
```

## Performance Tips

### Best Practices

1. **Group Similar Tasks**: Batch tasks with same imports together for higher cache hit rates
2. **Monitor Hit Rates**: Aim for 80%+ cache hit rate for optimal performance
3. **Tune Workers**: Set `WORKER_POOL_SIZE` ≈ 0.8 × CPU cores
4. **Adjust Replicas**: 4-8 replicas usually sufficient for HTTP handling
5. **Cache Size**: `MAX_CACHED_ENVS=3-10` per worker is optimal

### Expected Performance

- **Cold start** (cache miss): ~3.5s per task (loading imports)
- **Cache hit**: ~0.05s per task (reusing environment)
- **Throughput**: 50-200 codes/s depending on complexity and cache hit rate
- **Cache hit rate**: 80-95% for typical workloads

## Health Checks

```python
import requests

# Check server status
health = requests.get("http://localhost:8000/health").json()
print(f"Status: {health['status']}")
print(f"Workers: {health['num_workers']}")
print(f"Cache enabled: {health['cache_enabled']}")

# Get Ray cluster stats
ray_stats = requests.get("http://localhost:8000/stats/ray").json()
print(f"CPU utilization: {ray_stats['usage']['cpu_utilization']:.1f}%")
print(f"Memory used: {ray_stats['usage']['memory_gb_used']:.1f}GB")
```

## Troubleshooting

### Low Cache Hit Rate

If cache hit rate < 50%:
1. Check if tasks have diverse imports
2. Increase `MAX_CACHED_ENVS` in config
3. Consider increasing `max_tasks_per_worker` to concentrate tasks

### High Memory Usage

If workers consume too much memory:
1. Reduce `WORKER_POOL_SIZE`
2. Reduce `MAX_CACHED_ENVS` per worker
3. Enable `HARD_ENFORCE_MEMORY_LIMIT`

### Slow Throughput

If throughput < 10 codes/s:
1. Check CPU utilization (should be > 60%)
2. Verify workers are not overloaded (check `/stats/ray`)
3. Increase `WORKER_POOL_SIZE` if CPUs are available
4. Clear cache and restart if stale

