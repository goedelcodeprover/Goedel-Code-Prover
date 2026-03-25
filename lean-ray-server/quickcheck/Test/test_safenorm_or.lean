import Quickcheck

/-!
# SafeNorm and `Or` tests

How SafeNorm handles expressions inside `Or`.
-/

-- Example 1: `Or` with a simplifiable inner expression
def test_or_with_simplifiable (x : Nat) : Prop :=
  (∀ k, k < 3 → k < x) ∨ (x = 0)

-- Example 2: `False` inside `Or`
def test_or_with_false (x : Nat) : Prop :=
  False ∨ (x < 100)

-- Example 3: `True` inside `Or`
def test_or_with_true (x : Nat) : Prop :=
  (x = 999) ∨ True

-- Test: SafeNorm should simplify inside `Or`
set_option trace.quickcheck.safenorm true in
theorem test1 : test_or_with_simplifiable 10 := by
  unfold test_or_with_simplifiable
  -- SafeNorm unfolds `∀ k < 3` but does not split `Or`
  quickcheck (config := { enableSafeNorm := true })

-- Test: SafeNorm should simplify `False ∨ P` to `P`
set_option trace.quickcheck.safenorm true in
theorem test2 : test_or_with_false 50 := by
  unfold test_or_with_false
  -- SafeNorm should reduce `False ∨ (x < 100)` to `(x < 100)`
  quickcheck (config := { enableSafeNorm := true })

-- Test: SafeNorm should simplify `P ∨ True` to `True`
set_option trace.quickcheck.safenorm true in
theorem test3 : test_or_with_true 1 := by
  unfold test_or_with_true
  -- SafeNorm should reduce `(x = 999) ∨ True` to `True`
  quickcheck (config := { enableSafeNorm := true })

/-
## Example using `defaultRulesWithOr`

For deeper normalization inside `Or`, apply `SafeNormOr` manually:
-/

-- Manually apply SafeNorm with Or rules
example : test_or_with_simplifiable 10 := by
  unfold test_or_with_simplifiable
  -- Manual SafeNorm
  have : (∀ k, k < 3 → k < 10) ∨ (10 = 0) := by
    left
    intro k hk
    omega
  exact this
