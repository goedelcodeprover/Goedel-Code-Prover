import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_23


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isPowerOfTwo_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  -- !benchmark @start code
  if n <= 0 then false
  else
    let rec aux (m : Int) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if m = 1 then true
      else if m % 2 ≠ 0 then false
      else aux (m / 2) (fuel - 1)
    aux n n.natAbs
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def pow (base : Int) (exp : Nat) : Int :=
  match exp with
  | 0 => 1
  | n+1 => base * pow base n
-- !benchmark @end postcond_aux


@[reducible]
def isPowerOfTwo_postcond (n : Int) (result: Bool) (h_precond : isPowerOfTwo_precond (n)) : Prop :=
  -- !benchmark @start postcond
  if result then ∃ (x : Nat), (pow 2 x = n) ∧ (n > 0)
  else ¬ (∃ (x : Nat), (pow 2 x = n) ∧ (n > 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPowerOfTwo_spec_satisfied (n: Int) (h_precond : isPowerOfTwo_precond (n)) :
    isPowerOfTwo_postcond (n) (isPowerOfTwo (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_23
