# `max_env_reuse_count` performance test

## Purpose

Measure how different `max_env_reuse_count` values affect Lean verification latency and pick a good setting.

## Background

`max_env_reuse_count` caps how many times a cached environment may be reused:
- **Too low:** frequent env refresh, high startup cost
- **Too high:** possible leaks/fragmentation, slower runs
- **Sweet spot:** found experimentally

## Modes

### 1. Auto (recommended)

Tests the **current** server config for a quick read:

```bash
cd /local/home/zenali/Code-Prover/lean-ray-server
python test/test_reuse_count.py --mode auto --num-tests 100
```

**Sample output:**
```
📊 Test results
⏱️  Performance:
  - Total time: 45.2s
  - Mean per task: 452.0ms
  - Throughput: 2.21 tasks/s

🎯 Cache:
  - Hit rate: 85.3%
```

### 2. Manual (deeper)

Compare several `max_env_reuse_count` values:

```bash
python test/test_reuse_count.py --mode manual --num-tests 50 --reuse-counts 5 10 20 50 100
```

**Flow:**
1. Script asks you to set `MAX_ENV_REUSE_COUNT=5`
2. Edit `start_server.sh`:
   ```bash
   export MAX_ENV_REUSE_COUNT=5
   ```
3. Restart:
   ```bash
   bash start_server.sh
   ```
4. Press Enter to run
5. Repeat for 10, 20, 50, 100

**Sample summary:**
```
📊 Comparison
Reuse count  Total(s)   Mean/task(ms)   Throughput   Hit rate   Mean CPU%
--------------------------------------------------------------------------------------------------
5            32.5        650.0             1.54           95.0%        45.2      
10           28.3        566.0             1.77           94.5%        48.1      
20           25.1        502.0             1.99           93.8%        51.3      
50           26.8        536.0             1.87           92.1%        49.7      
100          29.5        590.0             1.69           91.5%        47.2      

🏆 Takeaways:
  - ✅ Best: max_env_reuse_count = 20 (mean 502.0ms)
  - ❌ Worst: max_env_reuse_count = 5 (mean 650.0ms)
  - 🚀 Spread: 1.29x

💡 Suggestion: try max_env_reuse_count = 20
```

## CLI reference

| Flag | Default | Description |
|------|---------|-------------|
| `--mode` | `auto` | `auto` = current server config; `manual` = compare reuse counts |
| `--base-url` | `http://localhost:8000` | Server URL |
| `--num-tests` | `100` | Number of tasks (should exceed `max_env_reuse_count`) |
| `--reuse-counts` | `[5,10,20,50,100]` | Counts to try in manual mode |

## Reading results

### What to watch

1. **Mean time per task** — primary metric (lower is better)
2. **Throughput** — tasks/s (higher is better)
3. **Cache hit rate** — aim for > 80%
4. **CPU usage** — ~30–60% is often healthy

### Patterns

**Lower reuse is faster**
```
5 → 500ms
20 → 480ms
100 → 520ms
```
→ Env accumulation hurts; try 10–20.

**Higher reuse is faster**
```
5 → 600ms
20 → 550ms
100 → 520ms
```
→ Startup dominates; 100 may be fine.

**Middle best**
```
5 → 600ms
20 → 480ms
100 → 550ms
```
→ Balance around 20–50.

## Quick start

**Suspect current settings:**
```bash
python test/test_reuse_count.py --mode auto --num-tests 50
```

**Tune reuse count:**
```bash
python test/test_reuse_count.py --mode manual --num-tests 100 --reuse-counts 10 20 30 50 100
```

**Realistic load (auto uses `test_set.json`):**
```bash
python test/test_reuse_count.py --mode auto --num-tests 100
```

## Notes

1. **Duration:** manual mode needs several server restarts; ~1–2 minutes per run
2. **`num_tests`:** should be **>** `max_env_reuse_count` to see refresh behavior
3. **Fairness:** script clears cache between runs
4. **Noise:** avoid other heavy jobs on the machine during runs
