import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_39


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxOfList_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst.length > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  -- !benchmark @start code
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0  -- technically shouldn't happen if input is always non-empty
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail

  helper lst
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxOfList_postcond (lst : List Nat) (result: Nat) (h_precond : maxOfList_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  result ∈ lst ∧ ∀ x ∈ lst, x ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfList_spec_satisfied (lst: List Nat) (h_precond : maxOfList_precond (lst)) :
    maxOfList_postcond (lst) (maxOfList (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_39
