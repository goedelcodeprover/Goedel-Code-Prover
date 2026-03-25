import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_58


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s
-- !benchmark @end code_aux


def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  -- !benchmark @start code
  double_array_elements_aux s s 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  -- !benchmark @start postcond
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem double_array_elements_spec_satisfied (s: Array Int) (h_precond : double_array_elements_precond (s)) :
    double_array_elements_postcond (s) (double_array_elements (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_58
