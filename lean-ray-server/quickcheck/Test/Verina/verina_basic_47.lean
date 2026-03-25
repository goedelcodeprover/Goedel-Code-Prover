import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_47


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def arraySum_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def arraySum (a : Array Int) (h_precond : arraySum_precond (a)) : Int :=
  -- !benchmark @start code
  a.toList.sum
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def sumTo (a : Array Int) (n : Nat) : Int :=
  if n = 0 then 0
  else sumTo a (n - 1) + a[n - 1]!
-- !benchmark @end postcond_aux


@[reducible, simp]
def arraySum_postcond (a : Array Int) (result: Int) (h_precond : arraySum_precond (a)) :=
  -- !benchmark @start postcond
  result - sumTo a a.size = 0 ∧
  result ≥ sumTo a a.size
  -- !benchmark @end postcond


-- !benchmark @start proof_aux
theorem eq_of_sub_zero_and_ge (a b : Int) : a = b → a - b = 0 ∧ a ≥ b := by
  omega
-- !benchmark @end proof_aux


theorem arraySum_spec_satisfied (a: Array Int) (h_precond : arraySum_precond (a)) :
    arraySum_postcond (a) (arraySum (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_47
