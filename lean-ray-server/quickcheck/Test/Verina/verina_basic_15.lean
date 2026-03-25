import Quickcheck

namespace verina_basic_15


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def containsConsecutiveNumbers_postcond (a : Array Int) (result: Bool) (h_precond : containsConsecutiveNumbers_precond (a)) :=
  -- !benchmark @start postcond
  (∃ i, i < a.size - 1 ∧ a[i]! + 1 = a[i + 1]!) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem containsConsecutiveNumbers_spec_satisfied (a: Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    containsConsecutiveNumbers_postcond (a) (containsConsecutiveNumbers (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_15
