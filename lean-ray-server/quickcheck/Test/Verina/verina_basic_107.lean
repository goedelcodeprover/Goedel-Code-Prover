import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_107


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  (a + b) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_107
