import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_64


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  -- !benchmark @start code
  let rec helper (lst : List Nat) (target : Nat) : List Nat :=
    match lst with
    | [] => []
    | x :: xs =>
      let rest := helper xs target
      if x = target then rest else x :: rest
  helper lst target
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def removeElement_postcond (lst : List Nat) (target : Nat) (result: List Nat) (h_precond : removeElement_precond (lst) (target)): Prop :=
  -- !benchmark @start postcond
  -- 1. All elements equal to target are removed from the result.
  -- 2. All other elements are preserved in order.
  -- 3. No new elements are added.

  -- Helper predicate: result contains exactly the elements of lst that are not equal to target, in order
  let lst' := lst.filter (fun x => x ≠ target)
  result.zipIdx.all (fun (x, i) =>
    match lst'[i]? with
    | some y => x = y
    | none => false) ∧ result.length = lst'.length
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
-- !benchmark @end proof_aux


theorem removeElement_spec_satisfied (lst: List Nat) (target: Nat) (h_precond : removeElement_precond (lst) (target)):
    removeElement_postcond (lst) (target) (removeElement (lst) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_64
