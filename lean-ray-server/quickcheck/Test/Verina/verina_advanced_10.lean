import Quickcheck

namespace verina_advanced_10

-- Helper function to check if a number is prime
def isPrime (p : Nat) : Bool :=
  if p < 2 then false
  else
    let rec check (d : Nat) (fuel : Nat) : Bool :=
      if fuel = 0 then true  -- Safety: return true if fuel exhausted
      else if d * d > p then true
      else if p % d == 0 then false
      else check (d + 1) (fuel - 1)
    check 2 p

-- !benchmark @end precond_aux
@[reducible]
def findExponents_precond (n : Nat) (primes : List Nat) : Prop :=
  -- !benchmark @start precond
  primes.all (fun p => isPrime p)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findExponents (n : Nat) (primes : List Nat) (h_precond : findExponents_precond (n) (primes)) : List (Nat × Nat) :=
  -- !benchmark @start code
  let rec countFactors (n : Nat) (primes : List Nat) : List (Nat × Nat) :=
    match primes with
    | [] => []
    | p :: ps =>
      let (count, n') :=
        countFactor n p 0
      (p, count) :: countFactors n' ps

  countFactors n primes
  where

  countFactor : Nat → Nat → Nat → Nat × Nat
  | 0, _, count =>
    (count, 0)
  | n, p, count =>
    if h : n > 0 ∧ p > 1 then
      have : n / p < n :=
        Nat.div_lt_self h.1 h.2
      if n % p == 0 then
        countFactor (n / p) p (count + 1)
      else
        (count, n)
    else
      (count, n)
  termination_by n _ _ => n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def findExponents_postcond (n : Nat) (primes : List Nat) (result: List (Nat × Nat)) (h_precond : findExponents_precond (n) (primes)) : Prop :=
  -- !benchmark @start postcond
  (n = result.foldl (fun acc (p, e) => acc * p ^ e) 1) ∧
  result.all (fun (p, _) => p ∈ primes) ∧
  primes.all (fun p => result.any (fun pair => pair.1 = p))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findExponents_spec_satisfied (n: Nat) (primes: List Nat) (h_precond : findExponents_precond (n) (primes)) :
    findExponents_postcond (n) (primes) (findExponents (n) (primes) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_10
