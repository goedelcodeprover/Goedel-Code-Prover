import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_65


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  -- !benchmark @start code
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SquareRoot_postcond (N : Nat) (result: Nat) (h_precond : SquareRoot_precond (N)) :=
  -- !benchmark @start postcond
  result * result ≤ N ∧ N < (result + 1) * (result + 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SquareRoot_spec_satisfied (N: Nat) (h_precond : SquareRoot_precond (N)) :
    SquareRoot_postcond (N) (SquareRoot (N) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_65
