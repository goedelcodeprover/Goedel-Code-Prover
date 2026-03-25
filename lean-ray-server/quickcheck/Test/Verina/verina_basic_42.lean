import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_42


-- !benchmark @start solution_aux
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  -- !benchmark @start code
  List.length (List.filter isDigit s.toList)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  -- !benchmark @start postcond
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countDigits_spec_satisfied (s: String) (h_precond : countDigits_precond (s)) :
    countDigits_postcond (s) (countDigits (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_42
