import Quickcheck

/-!
# `preprocess` tactic tests

This file demonstrates what the `preprocess` tactic can do:

1. **Nested `match`**: recursively splits every `match`
2. **And (`∧`)**: splits into several goals; all must be proved
3. **Or (`∨`)**: not split; quickcheck tests all branches via `orTestable`
4. **Mixed**: combinations of `And` + `Or`

## Key behavior

- **And**: uses `constructor`, producing multiple goals (all must hold)
- **Or**: not split; quickcheck's `orTestable` tries every branch
- **match**: uses `split`, one goal per pattern
-/

-- Test case 1: nested `match`
def nested_match (x y : Nat) : Nat :=
  match x with
  | 0 => match y with
    | 0 => 0
    | _ => 1
  | _ => match y with
    | 0 => 2
    | _ => 3

-- Test case 2: `And` (every conjunct must be proved)
def test_and (x y : Nat) : Prop :=
  (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1)

-- Test case 3: `Or` (quickcheck exercises all branches)
def test_or (x : Nat) : Prop :=
  x = 0 ∨ x = 1 ∨ x = 2

-- Test case 5: `Or` completeness (first branch false, second true)
def test_or_completeness (x : Nat) : Prop :=
  x = 999 ∨ x < 100  -- first branch almost never holds; second is easy

-- Test case 4: pure `And` (several conditions)
def test_pure_and (x : Nat) : Prop :=
  x = 0 ∧ x < 1 ∧ x ≥ 0

set_option trace.quickcheck.split true in
theorem test_nested_match : nested_match 0 0 = 0 := by
  unfold nested_match
  preprocess
  -- Nested `match` becomes four goals
  all_goals rfl

set_option trace.quickcheck.split true in
theorem test_and_split : test_and 0 0 := by
  unfold test_and
  preprocess
  -- `And` splits into two goals; `Or` inside each is not split
  -- Two goals: `(x = 0 ∨ x = 1)` and `(y = 0 ∨ y = 1)`
  all_goals (left; rfl)

set_option trace.quickcheck.split true in
theorem test_or_split : test_or 0 := by
  unfold test_or
  preprocess
  -- `Or` stays one goal: `(x = 0 ∨ x = 1 ∨ x = 2)`
  left; rfl

-- Show `Or` completeness: even if the first disjunct fails, quickcheck tries the second
theorem test_or_completeness_check : test_or_completeness 50 := by
  unfold test_or_completeness
  preprocess
  -- `Or` not split; quickcheck tests both branches
  -- `(x = 999)` fails but `(x < 100)` succeeds
  right; omega

set_option trace.quickcheck.split true in
theorem test_pure_and_split : test_pure_and 0 := by
  unfold test_pure_and
  preprocess
  -- Pure `And` splits into three goals
  all_goals (first | rfl | omega)
