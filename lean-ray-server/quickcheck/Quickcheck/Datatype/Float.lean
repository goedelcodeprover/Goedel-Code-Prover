/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Quickcheck.Arbitrary
import Quickcheck.Sampleable

/-!
# Float Type Instances for Property-Based Testing

This module provides the necessary instances to use `Float` with Quickcheck's
property-based testing framework.

## Warning

**Floating-point numbers are problematic for formal verification:**
- Precision issues: `0.1 + 0.2 ≠ 0.3`
- Rounding errors accumulate in calculations
- Non-associative: `(a + b) + c ≠ a + (b + c)`
- Special values: `NaN`, `Infinity` behavior is tricky

## Recommendations

1. **Use `Rat` (rational numbers)** instead for exact arithmetic
2. **Use `Int` or `Nat`** if fractional parts aren't needed
3. **Define a custom fixed-point type** for controlled precision

## Usage

Once this module is imported, you can use `Float` in property tests:

```lean
import Quickcheck.Datatype.Float

example (x : Float) : x + 0.0 = x := by
  quickcheck (config := { enableSafeGuard := false })
  -- Note: SafeGuard will warn about Float usage by default
```

## Main definitions

* `Repr Float` instance - For printing Float values
* `Shrinkable Float` instance - For minimizing counterexamples
* `Arbitrary Float` instance - For generating random Float values
* `SampleableExt Float` instance - Automatically derived from the above

-/

namespace Quickcheck

-- Note: Repr Float already exists in Lean 4 core, so we don't redefine it
-- If it doesn't exist, uncomment the following:
-- instance : Repr Float where
--   reprPrec f _ := s!"{f}"

/-- Shrinkable instance for Float.

Shrinking strategy:
- If the float is 0.0, there's nothing smaller to try
- Otherwise, try half the value and 0.0
-/
instance : Shrinkable Float where
  shrink f :=
    if f == 0.0 then
      []
    else
      let half := f / 2.0
      [half, 0.0]

/-- Arbitrary instance for Float.

Generation strategy:
- Generate a random integer part within the size parameter
- Generate a random fractional part (0-99)
- Combine them to create a Float with both integer and fractional components
- This produces values like: -5.42, 3.17, 0.89, etc.

The size parameter controls the magnitude of the integer part.
-/
instance : Arbitrary Float where
  arbitrary := do
    -- Generate an integer within range based on size
    let size ← Gen.getSize
    let n : Int ← Arbitrary.arbitrary
    let frac : Nat ← Arbitrary.arbitrary
    -- Limit range to avoid excessively large numbers
    let n_bounded := if n.natAbs > size then n % (size + 1) else n
    let frac_bounded := frac % 100
    -- Construct Float: integer part + fractional part
    return Float.ofInt n_bounded + (Float.ofNat frac_bounded) / 100.0

-- SampleableExt instance is automatically derived via the `selfContained` default instance
-- which requires: Repr + Shrinkable + Arbitrary

end Quickcheck
