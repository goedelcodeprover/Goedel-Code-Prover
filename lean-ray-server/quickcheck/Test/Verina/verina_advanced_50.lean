import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_50


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def mergeSorted_precond (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a1.toList ∧ List.Pairwise (· ≤ ·) a2.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def mergeSorted (a1 : Array Nat) (a2 : Array Nat) : Array Nat :=
  -- !benchmark @start code
  Id.run <| do
    let mut i := 0
    let mut j := 0
    let mut result := #[]
    while i < a1.size ∧ j < a2.size do
      if a1[i]! ≤ a2[j]! then
        result := result.push a1[i]!
        i := i + 1
      else
        result := result.push a2[j]!
        j := j + 1
    while i < a1.size do
      result := result.push a1[i]!
      i := i + 1
    while j < a2.size do
      result := result.push a2[j]!
      j := j + 1
    return result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def mergeSorted_postcond (a1 : Array Nat) (a2 : Array Nat) (result: Array Nat) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧
  result.toList.isPerm (a1.toList ++ a2.toList)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeSorted_spec_satisfied (a1: Array Nat) (a2: Array Nat) :
    mergeSorted_postcond (a1) (a2) (mergeSorted (a1) (a2)) := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_50
