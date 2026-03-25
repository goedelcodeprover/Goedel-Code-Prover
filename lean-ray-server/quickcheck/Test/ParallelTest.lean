import Quickcheck

/-!
# Parallel Quickcheck examples

How to use the `numWorkers` option for parallel testing.
Parallel runs can speed up large test suites substantially.
-/

-- Example 1: basic parallel testing
-- Use 4 parallel workers; each runs a share of the test instances
theorem parallel_basic (a b c : Nat) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  quickcheck (config := {
    Quickcheck.Configuration.normal with
    numWorkers := 4,      -- 4 parallel workers
    numInst := 100,       -- 100 instances total (~25 per worker)
  })

-- Example 2: large-scale parallel testing
-- Suited to machines with many CPU cores
theorem parallel_extensive (a b c : Nat) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  quickcheck (config := {
    Quickcheck.Configuration.extensive with
    numWorkers := 8,            -- 8 parallel workers
    numInst := 1000,            -- 1000 instances total
    workerTimeout := some 60,   -- at most 60 seconds per worker
  })

-- Example 3: parallel testing with per-worker timeout
-- For complex tests that may time out
theorem parallel_with_timeout (xs : List Nat) : xs.reverse.reverse = xs := by
  quickcheck (config := {
    Quickcheck.Configuration.normal with
    numWorkers := 4,
    workerTimeout := some 30,   -- 30s timeout per worker
    maxSize := 50,              -- cap input size to avoid timeouts
  })

-- Example 4: serial vs parallel
-- Serial mode (default)
theorem sequential_test (a b : Nat) : a + b = b + a := by
  quickcheck (config := {
    numWorkers := 1,            -- serial (default)
    numInst := 100,
  })

-- Parallel mode
theorem parallel_test (a b : Nat) : a + b = b + a := by
  quickcheck (config := {
    numWorkers := 4,            -- parallel
    numInst := 100,
  })

-- Example 5: full configuration with parallel mode
-- Combine several options
theorem parallel_full_config (xs : List Int) (x : Int) :
    (x :: xs).length = xs.length + 1 := by
  quickcheck (config := {
    Quickcheck.Configuration.extensive with
    numWorkers := 8,            -- number of parallel workers
    numInst := 500,             -- total test instances
    maxSize := 100,             -- maximum input size
    workerTimeout := some 120,  -- worker timeout (seconds)
    onlyDecidable := true,      -- use Decidable instances only
    enableSafeNorm := true,     -- enable safe normalization
    quiet := true,              -- quiet (less output)
  })

-- Example 6: small, fast parallel run
-- For quickly checking simple properties
theorem parallel_quick (x y : Nat) : x + y = y + x := by
  quickcheck (config := {
    numWorkers := 2,            -- few workers
    numInst := 20,              -- few instances
    maxSize := 10,              -- small inputs
  })
