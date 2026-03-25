import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_28


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 2
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  -- !benchmark @start code
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isPrime_postcond (n : Nat) (result: Bool) (h_precond : isPrime_precond (n)) :=
  -- !benchmark @start postcond
  (result → (List.range' 2 (n - 2)).all (fun k => n % k ≠ 0)) ∧
  (¬ result → (List.range' 2 (n - 2)).any (fun k => n % k = 0))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isPrime_spec_satisfied (n: Nat) (h_precond : isPrime_precond (n)) :
    isPrime_postcond (n) (isPrime (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_28
