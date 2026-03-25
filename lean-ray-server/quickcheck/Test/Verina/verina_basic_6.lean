import Quickcheck

namespace verina_basic_6


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_6
