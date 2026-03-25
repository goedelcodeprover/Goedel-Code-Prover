import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_7


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfSquaresOfFirstNOddNumbers (n : Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) : Nat :=
  -- !benchmark @start code
  let rec loop (k : Nat) (sum : Nat) : Nat :=
    if k = 0 then
      sum
    else
      loop (k - 1) (sum + (2 * k - 1) * (2 * k - 1))
  loop n 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfSquaresOfFirstNOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  result - (n * (2 * n - 1) * (2 * n + 1)) / 3 = 0 ∧
  (n * (2 * n - 1) * (2 * n + 1)) / 3 - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumOfSquaresOfFirstNOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfSquaresOfFirstNOddNumbers_precond (n)) :
    sumOfSquaresOfFirstNOddNumbers_postcond (n) (sumOfSquaresOfFirstNOddNumbers (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_7
