# Quickcheck
A property testing framework for Lean 4 that integrates into the tactic framework.

## Usage
If you are using built in types Quickcheck is usually able to handle them already:
```lean
import Quickcheck

example (xs ys : Array Nat) : xs.size = ys.size → xs = ys := by
  /--
  ===================
  Found a counter-example!
  xs := #[0]
  ys := #[1]
  guard: 1 = 1
  issue: #[0] = #[1] does not hold
  (0 shrinks)
  -------------------
  -/
  quickcheck

#eval Quickcheck.Testable.check <| ∀ (xs ys : Array Nat), xs.size = ys.size → xs = ys
```

If you are defining your own type it needs instances of `Repr`, `Quickcheck.Shrinkable` and
`Quickcheck.SampleableExt` (or `Quickcheck.Arbitrary`):
```lean
import Quickcheck

open Quickcheck

structure MyType where
  x : Nat
  y : Nat
  h : x ≤ y
  deriving Repr

instance : Shrinkable MyType where
  shrink := fun ⟨x, y, _⟩ =>
    let proxy := Shrinkable.shrink (x, y - x)
    proxy.map (fun (fst, snd) => ⟨fst, fst + snd, by omega⟩)

instance : SampleableExt MyType :=
  SampleableExt.mkSelfContained do
    let x ← SampleableExt.interpSample Nat
    let xyDiff ← SampleableExt.interpSample Nat
    return ⟨x, x + xyDiff, by omega⟩

-- No counter example found
#eval Testable.check <| ∀ a b : MyType, a.y ≤ b.x → a.x ≤ b.y
```
For more documentation refer to the module docs.

## Parallel and Sequential Execution Modes

Quickcheck supports both **parallel (multi-threaded)** and **sequential (single-threaded)** execution modes:

### Parallel Mode (`numWorkers > 1`)

When `numWorkers` is set to a value greater than 1, Quickcheck runs tests in parallel using multiple workers:

```lean
quickcheck (config := { 
  numWorkers := 4,        -- Use 4 parallel workers
  numInst := 100,         -- Total test instances (distributed across workers)
  workerTimeout := some 60 -- Timeout per worker in seconds
})
```

**Features:**
- Tests are distributed across multiple workers for faster execution
- Each worker uses a different random seed for independent test generation
- `workerTimeout` is monitored using **wall-clock time** (`IO.monoMsNow`)
  - If the time limit is exceeded, the worker stops
- **Limitation**: Timeout checking cannot interrupt a test that is already running. If a single test case takes longer than the timeout, it will complete before the timeout is detected. The timeout prevents starting new tests after the limit is reached.

### Sequential Mode (`numWorkers = 1`, default)

When `numWorkers` is 1 (the default), Quickcheck runs tests sequentially:

```lean
quickcheck (config := { 
  numWorkers := 1,        -- Sequential execution (default)
  numInst := 100,
  workerTimeout := some 60 -- Timeout monitoring enabled in sequential mode
})
```

**Features:**
- Tests run one at a time in a single thread
- `workerTimeout` is monitored using **wall-clock time** (`IO.monoMsNow`)
- Uses the same timeout monitoring mechanism as parallel mode

**Timeout Monitoring:**
- Uses **wall-clock time** (`IO.monoMsNow`) to detect timeouts
- Timeout checks occur **before and after** each test case
- **Limitation**: Cannot interrupt a test that is already running (Lean 4's IO is cooperative)
- If a single test case execution exceeds the timeout, it will complete before timeout is detected
- The timeout mechanism prevents starting new tests after the limit is reached, but cannot cancel in-progress tests
- **For strict timeout enforcement** that can interrupt long-running operations, use external process-level timeout tools:
  ```bash
  timeout 60s lake env lean your_file.lean
  ```

## Configuration Options

Quickcheck provides a comprehensive `Configuration` structure to customize test behavior. All options have sensible defaults, so you can override only what you need:

```lean
quickcheck (config := {
  -- Basic test parameters
  numInst := 100,              -- Number of test instances to generate (default: 100)
  maxSize := 100,              -- Maximum size of generated values (default: 100)
  numRetries := 10,            -- Number of retries when preconditions fail (default: 10)
  
  -- Shrinking configuration
  maxShrinkDepth := some 100,  -- Maximum depth for shrinking counter-examples (default: some 100)
                                -- Set to `none` for unlimited shrinking
  
  -- Tracing and debugging
  traceDiscarded := false,     -- Trace values that didn't fulfill preconditions (default: false)
  traceSuccesses := false,    -- Trace values that fulfilled the property (default: false)
  traceShrink := false,        -- Trace shrinking steps (default: false)
  traceShrinkCandidates := false, -- Trace all candidates during shrinking (default: false)
  quiet := false,              -- Disable all output (default: false)
  
  -- Random seed
  randomSeed := none,          -- Hard-code random seed for reproducibility (default: none)
                                -- Set to `some n` to use a specific seed
  
  -- Safety and validation
  enableSafeGuard := false,   -- Check for unsafe partial functions like `getLast!`, `head!` (default: false)
                                -- When enabled, quickcheck will error if it detects unsafe operations
  
  -- Decidable mode
  onlyDecidable := false,      -- Only use Decidable instances, fail if not decidable (default: false)
                                -- Ensures O(1) decision time per test case
  decidableBound := none,      -- Bound for unbounded quantifiers in onlyDecidable mode (default: none)
                                -- When set to `some n`:
                                --   `∀ x : Int` becomes `∀ x : Int, -n ≤ x ∧ x ≤ n → ...`
                                --   `∀ x : Nat` becomes `∀ x : Nat, x ≤ n → ...`
  
  -- Safe normalization
  enableSafeNorm := false,     -- Enable safe normalization preprocessing (default: false)
                                -- Applies safe rewrite rules to simplify goals:
                                -- - Unrolls bounded quantifiers (∀ k < n → P k becomes P 0 ∧ ... ∧ P (n-1))
                                -- - Eliminates redundant conditions
                                -- - Transforms expensive patterns to decidable forms
  safeNormUnrollBound := 20,  -- Maximum value for unrolling bounded quantifiers (default: 20)
                                -- Set based on available memory and performance requirements
  
  -- Parallel execution
  numWorkers := 1,             -- Number of parallel workers (default: 1)
                                -- Set to > 1 for parallel testing
  workerTimeout := none        -- Timeout per worker in seconds (default: none)
                                -- Set to `some n` to enable timeout monitoring
})
```

### Predefined Configurations

Quickcheck provides several predefined configurations for common use cases:

```lean
-- Minimal configuration for quick smoke tests
quickcheck (config := Quickcheck.Configuration.minimal)
-- numInst := 5, maxSize := 10, numRetries := 1, maxShrinkDepth := some 5

-- Fast configuration for development
quickcheck (config := Quickcheck.Configuration.fast)
-- numInst := 20, maxSize := 30, numRetries := 3, maxShrinkDepth := some 20

-- Normal/standard configuration (default values)
quickcheck (config := Quickcheck.Configuration.normal)
-- numInst := 100, maxSize := 100, numRetries := 10, maxShrinkDepth := some 100

-- Extensive configuration for thorough testing
quickcheck (config := Quickcheck.Configuration.extensive)
-- numInst := 1000, maxSize := 100, numRetries := 20, maxShrinkDepth := some 200

-- Verbose configuration with all tracing enabled
quickcheck (config := Quickcheck.Configuration.verbose)
-- traceDiscarded := true, traceSuccesses := true, traceShrink := true, traceShrinkCandidates := true
```

### Configuration Option Details

#### Basic Test Parameters

- **`numInst`**: Total number of test instances to generate. Tests are distributed across workers if `numWorkers > 1`.
- **`maxSize`**: Controls the maximum size of generated values. Larger values may find more complex counter-examples but take longer to test.
- **`numRetries`**: When a generated value doesn't satisfy preconditions (e.g., `x < 10` in `∀ x : Nat, x < 10 → P x`), quickcheck will retry up to this many times before giving up.

#### Shrinking Configuration

- **`maxShrinkDepth`**: Limits how deep the shrinking process goes. Shrinking tries to find smaller counter-examples. Set to `none` for unlimited shrinking (may be slow for complex types).

#### Tracing Options

All tracing options are useful for debugging:
- **`traceDiscarded`**: Shows values that were generated but didn't satisfy preconditions
- **`traceSuccesses`**: Shows values that successfully passed the test
- **`traceShrink`**: Shows each shrinking step
- **`traceShrinkCandidates`**: Shows all candidate values considered during shrinking

#### Safety Features

- **`enableSafeGuard`**: Detects unsafe partial functions (like `List.getLast!`, `Array.get!`) before testing. If detected, quickcheck will error with suggestions for safe alternatives.
- **`onlyDecidable`**: Forces quickcheck to only use `Decidable` instances. If a proposition is not decidable, quickcheck will fail immediately rather than using random sampling. This ensures O(1) decision time per test case.

#### Safe Normalization

- **`enableSafeNorm`**: Applies safe rewrite rules to simplify propositions before testing. This can significantly speed up testing by:
  - Unrolling small bounded quantifiers (e.g., `∀ k < 5 → P k` becomes `P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4`)
  - Simplifying expressions using `@[quickcheck]` marked theorems
- **`safeNormUnrollBound`**: Maximum value for unrolling bounded quantifiers. Higher values can handle more cases but may consume more memory.

#### Parallel Execution

- **`numWorkers`**: Number of parallel workers. Each worker uses a different random seed. Tests are distributed evenly across workers.
- **`workerTimeout`**: Timeout per worker in seconds. Uses wall-clock time monitoring. Cannot interrupt tests already running, but prevents starting new tests after timeout.

**Deriving Instance for `Arbitrary`** (for algebraic data types)              
Users can write `deriving Arbitrary` after an inductive type definition, i.e.
```lean 
inductive Foo where
  ...
  deriving Arbitrary
```

Alternatively, users can also write `deriving instance Arbitrary for T1, ..., Tn` as a top-level command to derive `Arbitrary` instances for types `T1, ..., Tn` simultaneously.

