import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_11


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0
-- !benchmark @end code_aux


def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  -- !benchmark @start code
  let n := lst.length
  let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
  match majority with
  | some x => x
  | none => -1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findMajorityElement_postcond (lst : List Int) (result: Int) (h_precond : findMajorityElement_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  let count := fun x => (lst.filter (fun y => y = x)).length
  let n := lst.length
  let majority := count result > n / 2 ∧ lst.all (fun x => count x ≤ n / 2 ∨ x = result)
  (result = -1 → lst.all (count · ≤ n / 2) ∨ majority) ∧
  (result ≠ -1 → majority)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findMajorityElement_spec_satisfied (lst: List Int) (h_precond : findMajorityElement_precond (lst)) :
    findMajorityElement_postcond (lst) (findMajorityElement (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_11
