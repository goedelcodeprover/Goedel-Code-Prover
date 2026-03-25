import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_72


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  -- !benchmark @start code
  if n == 0 then 0
  else if n % 2 == 0 then 2
  else if n % 3 == 0 then 3
  else if n % 5 == 0 then 5
  else if n % 7 == 0 then 7
  else 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def singleDigitPrimeFactor_postcond (n : Nat) (result: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Prop :=
  -- !benchmark @start postcond
  result ∈ [0, 2, 3, 5, 7] ∧
  (result = 0 → (n = 0 ∨ [2, 3, 5, 7].all (n % · ≠ 0))) ∧
  (result ≠ 0 → n ≠ 0 ∧ n % result == 0 ∧ (List.range result).all (fun x => x ∈ [2, 3, 5, 7] → n % x ≠ 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem singleDigitPrimeFactor_spec_satisfied (n: Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    singleDigitPrimeFactor_postcond (n) (singleDigitPrimeFactor (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_72
