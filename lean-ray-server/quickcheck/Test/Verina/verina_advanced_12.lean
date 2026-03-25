import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_12


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Int :=
  -- !benchmark @start code
  let rec helper (seen : List Int) (rem : List Int) : Int :=
    match rem with
    | [] => -1
    | h :: t => if seen.contains h then h else helper (h :: seen) t
  helper [] lst
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def firstDuplicate_postcond (lst : List Int) (result: Int) (h_precond : firstDuplicate_precond (lst)) : Prop :=
  -- !benchmark @start postcond
  -- if result = -1, then lst does not contain any duplicates
  (result = -1 → List.Nodup lst) ∧
  -- if result is not -1, then it is the first duplicate in lst
  (result ≠ -1 →
    lst.count result > 1 ∧
    (lst.filter (fun x => lst.count x > 1)).head? = some result
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem firstDuplicate_spec_satisfied (lst: List Int) (h_precond : firstDuplicate_precond (lst)) :
    firstDuplicate_postcond (lst) (firstDuplicate (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_12
