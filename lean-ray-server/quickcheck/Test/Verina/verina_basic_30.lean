import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_30


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  a.mapIdx (fun i x => x % b[i]!)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def elementWiseModulo_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  (∀ i, i < result.size → result[i]! = a[i]! % b[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem elementWiseModulo_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    elementWiseModulo_postcond (a) (b) (elementWiseModulo (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_30
