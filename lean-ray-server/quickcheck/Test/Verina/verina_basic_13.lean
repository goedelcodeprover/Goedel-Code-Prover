import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_13


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  -- !benchmark @start code
  a.map (fun x => x * x * x)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def cubeElements_postcond (a : Array Int) (result: Array Int) (h_precond : cubeElements_precond (a)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧
  (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem cubeElements_spec_satisfied (a: Array Int) (h_precond : cubeElements_precond (a)) :
    cubeElements_postcond (a) (cubeElements (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_13
