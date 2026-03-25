import Quickcheck

namespace verina_basic_48


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPerfectSquare (n : Nat) : Bool :=
  -- !benchmark @start code
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPerfectSquare_postcond (n : Nat) (result : Bool) : Prop :=
  -- !benchmark @start postcond
  result ↔ ∃ i : Nat, i * i = n
  -- !benchmark @end postcond

theorem isPerfectSquare_spec_satisfied (n : Nat) :
    isPerfectSquare_postcond n (isPerfectSquare n) := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with decidableBound := some 1000, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_48
