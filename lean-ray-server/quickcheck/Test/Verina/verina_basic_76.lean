import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_76


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  -- !benchmark @start code
  if x < y then x else y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def myMin_postcond (x : Int) (y : Int) (result: Int) (h_precond : myMin_precond (x) (y)) :=
  -- !benchmark @start postcond
  (x ≤ y → result = x) ∧ (x > y → result = y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem myMin_spec_satisfied (x: Int) (y: Int) (h_precond : myMin_precond (x) (y)) :
    myMin_postcond (x) (y) (myMin (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_76
