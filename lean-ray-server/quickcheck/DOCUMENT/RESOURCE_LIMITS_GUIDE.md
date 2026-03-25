# Resource limits guide

## New behavior

Error handling has been added so a single worker crash does not take down the whole process.

## Configuration options

### workerTimeout (optional)

```lean
quickcheck (config := { 
  Quickcheck.Configuration.extensive with 
  workerTimeout := some 60  -- at most 60 seconds per worker (not fully wired; see below)
})
```

**Note:** Lean 4 has no built-in timeout API. `workerTimeout` is defined in config but needs external tooling to enforce.

### workerMemoryLimit (optional)

```lean
quickcheck (config := { 
  Quickcheck.Configuration.extensive with 
  workerMemoryLimit := some 512  -- at most 512 MB per worker (OS support required)
})
```

**Note:** Memory limits need OS-level support; in practice complexity is often controlled indirectly via `maxSize`.

## Practical usage

### Method 1: External tools (recommended)

When running Lean files, use system utilities:

```bash
# Limit time (60s) and memory (512MB)
timeout 60s prlimit --as=512000000 -- lake env lean Test/Verina/verina_advanced_43.lean
```

Or `ulimit`:

```bash
# Memory cap (512MB = 524288 KB)
ulimit -v 524288
timeout 60s lake env lean Test/Verina/verina_advanced_43.lean
```

### Method 2: Limit computational complexity via config (most effective)

```lean
quickcheck (config := { 
  Quickcheck.Configuration.extensive with 
  onlyDecidable := true, 
  enableSafeNorm := true, 
  quiet := true, 
  numWorkers := 4,      -- fewer workers
  maxSize := 8,          -- bound data size; avoids 2^100-style blowups
  numInst := 100         -- fewer test instances
})
```

### Method 3: Combine both

```lean
theorem maxStrength_spec_satisfied (nums: List Int) (h_precond : maxStrength_precond (nums)) :
    maxStrength_postcond (nums) (maxStrength (nums) h_precond) h_precond := by
  unfold maxStrength_postcond
  quickcheck (config := { 
    Quickcheck.Configuration.extensive with 
    onlyDecidable := true, 
    enableSafeNorm := true, 
    quiet := true, 
    numWorkers := 4,           -- cap concurrency
    maxSize := 8,              -- cap data size
    workerTimeout := some 30,  -- documented; enforce with external tool
    workerMemoryLimit := some 256  -- documented; enforce with external tool
  })
```

Then wrap the run:

```bash
timeout 120s prlimit --as=1024000000 -- lake env lean Test/Verina/verina_advanced_43.lean
```

## Error-handling changes

### Before

- One worker crash (memory/stack) → whole process died
- 64 workers all computing `2^100` → OOM killer killed the process

### After

- One worker crash → caught as `gaveUp`, other workers continue
- The process no longer dies from a single worker failure

## Recommended configurations

### Heavy work (e.g. `2^n` subsets)

```lean
quickcheck (config := { 
  Quickcheck.Configuration.fast with 
  onlyDecidable := true, 
  enableSafeNorm := true, 
  quiet := true, 
  numWorkers := 2,      -- low concurrency
  maxSize := 6,          -- small data: 2^6 = 64 subsets
  numInst := 20
})
```

### Medium complexity

```lean
quickcheck (config := { 
  Quickcheck.Configuration.extensive with 
  onlyDecidable := true, 
  enableSafeNorm := true, 
  quiet := true, 
  numWorkers := 4,
  maxSize := 8,          -- medium: 2^8 = 256 subsets
  numInst := 100
})
```

### Light work

```lean
quickcheck (config := { 
  Quickcheck.Configuration.extensive with 
  onlyDecidable := true, 
  enableSafeNorm := true, 
  quiet := true, 
  numWorkers := 8,       -- can use more workers
  maxSize := 10,         -- 2^10 = 1024 subsets
  numInst := 200
})
```

## OS-level resource examples

### systemd-run

```bash
# Cap CPU time, memory, and task count
systemd-run --scope \
  --property=CPUQuota=200% \
  --property=MemoryMax=2G \
  --property=TasksMax=64 \
  lake env lean Test/Verina/verina_advanced_43.lean
```

### cgroups v2

```bash
# Create cgroup
sudo mkdir -p /sys/fs/cgroup/test
echo "+cpu +memory" | sudo tee /sys/fs/cgroup/test/cgroup.subtree_control

# Set limits
echo "200000" | sudo tee /sys/fs/cgroup/test/cpu.max  # 200% CPU
echo "2147483648" | sudo tee /sys/fs/cgroup/test/memory.max  # 2GB

# Run
echo $$ | sudo tee /sys/fs/cgroup/test/cgroup.procs
lake env lean Test/Verina/verina_advanced_43.lean
```

## Monitoring

In another terminal:

```bash
# Memory
watch -n 1 'free -h'

# Processes
watch -n 1 'ps aux | grep lean | head -10'

# System
htop
```

## Summary

1. **Error handling:** implemented — worker crashes do not kill the process
2. **Timeouts:** use external tools (`timeout`)
3. **Memory:** use external tools (`prlimit`, `ulimit`, `systemd-run`, …)
4. **Best practice:** tune `maxSize` and `numWorkers` to limit work
