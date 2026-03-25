import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_55


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  if a = b then true else false
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a = b → result = true) ∧ (a ≠ b → result = false)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Compare_spec_satisfied (a: Int) (b: Int) (h_precond : Compare_precond (a) (b)) :
    Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_55
