# Lean Verifier Server — stress test

## Stress test

Runs **10,000** Lean snippets from `test_set.json` under high concurrency.

---

## Test data format

`test/test_set.json`:
```json
[
  {
    "id": 0,
    "name": "test_case_name",
    "code": "import Mathlib\n\ndef add ..."
  },
  ...
]
```

---

## Running the stress test

### Basic

```bash
# All 10,000 cases
python test/test_server.py --test stress

# Custom server URL
python test/test_server.py --test stress --url http://localhost:8000
```

### Limit sample count

```bash
python test/test_server.py --test stress --max-samples 100
python test/test_server.py --test stress --max-samples 1000
```

### Load shaping

```bash
# Spread work across workers
python test/test_server.py --test stress --max-tasks-per-worker 2

# Fewer workers, higher cache reuse
python test/test_server.py --test stress --max-tasks-per-worker 50

# Server default (often 10)
python test/test_server.py --test stress
```

### Full example

```bash
python test/test_server.py \
  --test stress \
  --url http://localhost:8000 \
  --test-file test/test_set.json \
  --max-samples 1000 \
  --max-tasks-per-worker 10
```

---

## Output

Typical summary:

```
================================================================================
🔥 Stress test: full test_set.json
================================================================================
📂 Loaded: 10000 cases
🎯 Config:
  - Total cases: 10000
  - Batch size: 100
  - Batch count: 100
🗑️  Clearing cache...
✅ Cache cleared
🚀 Starting stress test...

================================================================================
📊 Stress test results
================================================================================
🎯 Verification:
  - Total: 10000
  - ✅ Pass (no sorry): 8500 (85.0%)
  - ⚠️  Pass (with sorry): 9200 (92.0%)
  - ❌ Fail: 1500 (15.0%)

⚡ Performance:
  - Total time: 125.34s (2.1 min)
  - Mean throughput: 79.78 codes/s
  - Mean per case: 12.5ms

💻 CPU:
  - Mean: 75.3%
  - Max: 92.1%
  - Min: 45.2%

🎯 Cache:
  - Hits: 9520
  - Misses: 480
  - Hit rate: 95.2%
  - Est. speedup vs no cache: 15.3x

⚙️  Config:
  - Workers: 64
  - Replicas: 4
  - Cache enabled: True
  - Max cached envs: 10
  - Max tasks per worker: 10
================================================================================
✅ Stress test OK — pass rate: 85.0%
```

---

## Flags

| Flag | Default | Description |
|------|---------|-------------|
| `--url` | `http://localhost:8000` | Server base URL |
| `--test-file` | `test/test_set.json` | JSON test file |
| `--max-samples` | `None` (all) | Cap number of cases |
| `--max-tasks-per-worker` | `None` (server default) | Tasks bound per worker |

---

## Tuning notes

### 1. Small run (sanity)

```bash
python test/test_server.py --test stress --max-samples 100
```

**Expect:** ~5–10s — confirms server is up.

### 2. Medium (baseline)

```bash
python test/test_server.py --test stress --max-samples 1000 --max-tasks-per-worker 10
```

**Expect:** ~50–100s — throughput and cache behavior.

### 3. Full stress

```bash
python test/test_server.py --test stress
```

**Expect:** ~5–15 min depending on hardware.

### 4. High concurrency

```bash
python test/test_server.py --test stress --max-samples 1000 --max-tasks-per-worker 2
```

- Higher parallelism
- Lower cache hit rate
- Stresses concurrent handling

### 5. Cache-focused

```bash
python test/test_server.py --test stress --max-samples 1000 --max-tasks-per-worker 50
```

- Higher hit rate (often 95%+)
- Less parallelism
- Stresses caching

---

## Rough benchmarks

**64 workers, 4 replicas** (illustrative):

| Scale | Samples | Time | Throughput | Hit rate |
|-------|---------|------|------------|----------|
| Small | 100 | 5–10s | 10–20 codes/s | 50–70% |
| Medium | 1,000 | 50–100s | 10–20 codes/s | 80–90% |
| Large | 10,000 | 5–15 min | 10–30 codes/s | 90–95% |

**Notes:** Cold start lowers hit rate; repeat runs improve it. Throughput depends on CPU, RAM, and network.

---

## Troubleshooting

### 1. Timeouts

```
❌ Request timed out (> 1 hour)
```

- Lower `--max-samples`
- Raise `WORKER_POOL_SIZE`
- Check for stuck server

### 2. OOM / worker crashes

- Lower `WORKER_POOL_SIZE`
- Lower `MAX_CACHED_ENVS`
- Raise `REPL_MEMORY_LIMIT_GB`

### 3. Low hit rate

```
🎯 Cache:
  - Hit rate: 15.0%  ← too low
```

- Increase `--max-tasks-per-worker`
- Increase `MAX_CACHED_ENVS`
- Check for very diverse imports across cases

### 4. Low throughput

```
⚡ Performance:
  - Mean throughput: 2.15 codes/s  ← slow
```

- More workers
- Check CPU is not idle
- Rule out network bottlenecks
- Sometimes **lower** `max_tasks_per_worker` increases effective concurrency

---

## Logs

```bash
python test/test_server.py --test stress 2>&1 | tee stress_test_$(date +%Y%m%d_%H%M%S).log
```

---

## Success criteria

Treat the run as **passing** when:
- Pass rate ≥ 80% (`is_valid_no_sorry`)
- No server crash
- No timeout errors

---

## Example session

```bash
cd /local/home/zenali/Code-Prover/lean-ray-server
bash start_server.sh
# ~30s for startup

python test/test_server.py --test stress --max-samples 100
python test/test_server.py --test stress
```
