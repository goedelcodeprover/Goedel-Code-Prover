import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_19


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isSorted_postcond (a : Array Int) (result: Bool) (h_precond : isSorted_precond (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size - 1) → a[i] ≤ a[i + 1]) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isSorted_spec_satisfied (a: Array Int) (h_precond : isSorted_precond (a)) :
    isSorted_postcond (a) (isSorted (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })


  -- !benchmark @end proof
end verina_basic_19
