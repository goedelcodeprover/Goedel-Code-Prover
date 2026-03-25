import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_5


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  -- !benchmark @start code
  a * b
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  -- !benchmark @start postcond
  result - a * b = 0 ∧ a * b - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_5
