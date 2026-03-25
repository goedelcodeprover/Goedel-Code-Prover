import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_14


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  -- !benchmark @start code
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  -- !benchmark @start postcond
  result ↔ (∃ m:Nat, n=4^m)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with decidableBound := some 1000, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_14
