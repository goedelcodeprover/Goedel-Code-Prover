import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_41


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  -- !benchmark @start postcond
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_41
