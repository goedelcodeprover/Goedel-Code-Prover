import Quickcheck

open Quickcheck

/-!
# Performance test examples

Examples showing quickcheck performance after optimizations.

## Comparing configurations
-/

-- Example 1: list property (false — triggers shrinking)
example : ∀ (xs : List Nat), xs.length < 5 := by
  -- fast config
  quickcheck (config := { Quickcheck.Configuration.fast with quiet := false })
  sorry

-- Example 2: array property
example : ∀ (xs : Array Int), xs.size = 0 ∨ xs[0]! ≥ 0 := by
  -- minimal config
  quickcheck (config := { Quickcheck.Configuration.minimal with quiet := false })
  sorry

-- Example 3: string property
example : ∀ (s : String), s.length < 10 := by
  -- default config
  quickcheck
  sorry

-- Example 4: nested lists
example : ∀ (xss : List (List Nat)), xss.length < 3 := by
  -- custom: cap size and shrink depth
  quickcheck (config := { numInst := 10, maxSize := 20, maxShrinkDepth := some 10 })
  sorry

/-!
## Timing comparisons

Use `#time` to compare configs:

```lean
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) Quickcheck.Configuration.minimal
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) Quickcheck.Configuration.fast
#time #eval Testable.check (∀ xs : List Nat, xs.length < 50) {}  -- default
```

## Shrink optimization

The properties below find a counterexample and shrink it:
-/

-- Finds a counterexample and shows optimized shrinking
#eval Testable.check
  (∀ (xs : List Nat), xs.sum < 100)
  { Quickcheck.Configuration.fast with traceShrink := true }

-- Large-array shrink behavior
#eval Testable.check
  (∀ (xs : Array Nat), xs.size < 10)
  { Quickcheck.Configuration.fast with traceShrink := true }

/-!
## Memory / generation limits

How size limits avoid huge values:

Before optimization, this might try enormous lists.
After optimization, list length stays within a reasonable bound.
-/

-- List generation size cap
#eval do
  let xs : List Nat ← Gen.run (Gen.listOf Arbitrary.arbitrary (maxSize := some 50)) 100
  IO.println s!"Generated list of length: {xs.length}"

-- Array generation size cap
#eval do
  let xs : Array Nat ← Gen.run (Gen.arrayOf Arbitrary.arbitrary (maxSize := some 50)) 100
  IO.println s!"Generated array of size: {xs.size}"

/-!
## Suggested testing strategy

1. **Development**: `Quickcheck.Configuration.fast` for quick iteration
2. **CI**: `Quickcheck.Configuration.minimal` for fast smoke tests
3. **Nightly**: default or stricter settings for deeper coverage
4. **Debugging failures**: `Quickcheck.Configuration.verbose` for detail
-/
