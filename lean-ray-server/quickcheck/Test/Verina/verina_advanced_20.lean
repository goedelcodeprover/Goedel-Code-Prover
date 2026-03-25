import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_20


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isItEight_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  -- !benchmark @start code
  let rec hasDigitEight (m : Nat) : Bool :=
    if m <= 0 then false
    else if m % 10 == 8 then true
    else hasDigitEight (m / 10)
    termination_by m

  let absN := Int.natAbs n
  n % 8 == 0 || hasDigitEight absN
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def isItEight_postcond (n : Int) (result: Bool) (h_precond : isItEight_precond (n)) : Prop :=
  -- !benchmark @start postcond
  let absN := Int.natAbs n;
  (n % 8 == 0 ∨ ∃ i, absN / (10^i) % 10 == 8) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isItEight_spec_satisfied (n: Int) (h_precond : isItEight_precond (n)) :
    isItEight_postcond (n) (isItEight (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with decidableBound := some 1000, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_20
