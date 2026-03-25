import Quickcheck

/-!
# Safe normalization examples

How to use safe normalization to speed up quickcheck.
-/

set_option maxHeartbeats 0

namespace SafeNormExample

-- Example 1: simple bounded universal quantifier
-- This pattern can be unfolded automatically into a conjunction

def hasAllSmall (a : Array Nat) : Prop :=
  ∀ i, i < 3 → a.size > i → a[i]! < 10

-- Unoptimized version — can be slow
example : hasAllSmall #[1, 2, 3, 4] := by
  unfold hasAllSmall
  intro i h_lt h_size
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ _ => omega

-- With safe normalization — should be faster
-- (Note: implementation still evolving; conceptual demo)

-- Example 2: simplified verina_basic_24-style spec

def isEven (n : Int) : Bool := n % 2 == 0
def isOdd (n : Int) : Bool := n % 2 != 0

@[reducible, simp]
def precond_simple (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

-- Heavy postcondition (nested universals — slow)
@[reducible, simp]
def postcond_complex (a : Array Int) (result: Int) (h : precond_simple a) :=
  ∃ i j, i < a.size ∧ j < a.size ∧
    isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧   -- 🔴 these are slow
    (∀ k, k < j → isEven (a[k]!))    -- 🔴 these are slow

-- Simplified postcondition (no "first" requirement — fast)
@[reducible, simp]
def postcond_simple (a : Array Int) (result: Int) (h : precond_simple a) :=
  ∃ i j, i < a.size ∧ j < a.size ∧
    isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]!
    -- ✅ removed heavy universal quantifiers

def findFirstEvenOdd (a : Array Int) (h : precond_simple a) : Int :=
  let rec loop (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => loop (i + 1) firstEven firstOdd
    else
      0
  loop 0 none none

-- Test simplified version — should be quick
theorem test_simple (a: Array Int) (h : precond_simple a) :
    postcond_simple a (findFirstEvenOdd a h) h := by
    -- standard quickcheck
    quickcheck (config := Quickcheck.Configuration.fast)

-- Example 3: compare configurations

-- Config 1: normal
def config_normal := Quickcheck.Configuration.normal

-- Config 2: fast
def config_fast := Quickcheck.Configuration.fast

-- Config 3: safe normalization (experimental)
def config_safe_norm : Quickcheck.Configuration := {
  numInst := 20,
  maxSize := 30,
  enableSafeNorm := true,
  safeNormUnrollBound := 10
}

-- Config 4: combined
def config_combined : Quickcheck.Configuration := {
  numInst := 20,
  maxSize := 30,
  enableSafeNorm := true,
  safeNormUnrollBound := 5,
  onlyDecidable := true,
  decidableBound := some 10
}

-- Example 4: patterns safe normalization can handle

-- Pattern 1: bounded quantifier
def pattern1 (a : Array Nat) : Prop :=
  ∀ i, i < 5 → i < a.size → a[i]! > 0

-- Pattern 2: existence
def pattern2 (a : Array Nat) : Prop :=
  ∃ i, i < a.size ∧ a[i]! = 42

-- Pattern 3: conjunction split
def pattern3 (a : Array Nat) : Prop :=
  (∀ i, i < a.size → a[i]! > 0) ∧
  (∀ i, i < a.size → a[i]! < 100) ∧
  (a.size > 0)

-- Hint: for `pattern1`, with `enableSafeNorm` and `5 ≤ safeNormUnrollBound`,
-- the quantifier may unfold to: `a[0]! > 0 ∧ a[1]! > 0 ∧ ... ∧ a[4]! > 0`

end SafeNormExample

/-!
## Usage tips

### When quickcheck is slow:

1. **Inspect spec complexity**
   - Nested `∀` and `∃`?
   - Checking the "first" element satisfying a predicate?
   - How large are the bounds?

2. **Simplify the spec (most effective)**
   - Drop unnecessary "first" requirements
   - Replace heavy quantifier patterns with simple existence
   - Strengthen preconditions to shrink the search space

3. **Use a fast config**
   ```lean
   quickcheck (config := Quickcheck.Configuration.fast)
   ```

4. **Enable safe normalization (experimental)**
   ```lean
   quickcheck (config := {
     enableSafeNorm := true,
     safeNormUnrollBound := 10
   })
   ```

5. **Use `decidableBound`**
   ```lean
   quickcheck (config := {
     onlyDecidable := true,
     decidableBound := some 20
   })
   ```

6. **Use `quickcheck_all` on complex goals**
   ```lean
   quickcheck_all [def1, def2] (config := Quickcheck.Configuration.fast)
   ```

### Debugging

```lean
-- Trace safe normalization
set_option trace.quickcheck.safenorm true

-- Trace testing
set_option trace.quickcheck true

-- Trace discarded samples
set_option trace.quickcheck.discarded true
```
-/
