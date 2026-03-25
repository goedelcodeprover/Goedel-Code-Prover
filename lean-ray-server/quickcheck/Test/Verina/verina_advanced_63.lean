import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_63


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  -- nums are sorted in non-decreasing order
  List.Pairwise (· ≤ ·) nums
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  -- !benchmark @start code
  match nums with
  | [] =>
    0
  | h :: t =>
    let init := h
    let initCount := 1
    let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
      match xs with
      | [] =>
        k
      | head :: tail =>
        let isDuplicate := head = prev
        if isDuplicate then
          countUniques prev tail k
        else
          let newK := k + 1
          countUniques head tail newK
    countUniques init t initCount
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def removeDuplicates_postcond (nums : List Int) (result: Nat) (h_precond : removeDuplicates_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  result - nums.eraseDups.length = 0 ∧
  nums.eraseDups.length ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem removeDuplicates_spec_satisfied (nums: List Int) (h_precond : removeDuplicates_precond (nums)) :
    removeDuplicates_postcond (nums) (removeDuplicates (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_63
