/-
Test file demonstrating the new Decidable instances for casesOn patterns.

These instances allow quickcheck to handle propositions that involve pattern matching
on Option, Prod, List, etc. when the scrutinee is a runtime value.

Key insight: Lean's `match` syntax is elaborated to a generated match function,
which is different from `casesOn`. Our Decidable instances work for `casesOn`.

For `match` syntax, either:
1. Unfold the function so the match can be simplified at compile time
2. Use `casesOn` syntax instead of `match`
-/

import Quickcheck

-- Example 1: Using casesOn explicitly (recommended when Decidable instance is needed)
def postcondWithCasesOn (nums : List Int) (target : Int) : Option (Nat × Nat) → Prop :=
  fun result => result.casesOn
    (List.Pairwise (fun a b => a + b ≠ target) nums)
    (fun p => p.casesOn (fun i j => i < j ∧ j < nums.length))

def myFunc (nums : List Int) (target : Int) : Option (Nat × Nat) := none

-- This works without unfolding myFunc!
theorem test_caseson (nums: List Int) (target: Int) :
    postcondWithCasesOn nums target (myFunc nums target) := by
  unfold postcondWithCasesOn  -- Only unfold postcond, not the function
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, quiet := true })

-- Example 2: Using match syntax requires unfolding the function
def postcondWithMatch (nums : List Int) (target : Int) (result: Option (Nat × Nat)) : Prop :=
  match result with
  | none => List.Pairwise (fun a b => a + b ≠ target) nums
  | some (i, j) => i < j ∧ j < nums.length

-- This requires unfolding BOTH postcond AND myFunc
theorem test_match (nums: List Int) (target: Int) :
    postcondWithMatch nums target (myFunc nums target) := by
  unfold postcondWithMatch myFunc  -- Must unfold both!
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, quiet := true })

-- Example 3: List.Pairwise works directly (it's already decidable)
theorem test_pairwise_direct (nums: List Int) (target: Int) :
    List.Pairwise (fun a b => a + b ≠ target) nums := by
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, quiet := true })
