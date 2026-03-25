import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_9


-- !benchmark @start solution_aux
def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  -- !benchmark @start precond
  d > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0
-- !benchmark @end code_aux


def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  -- !benchmark @start code
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
      go i' acc'
  go n 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def countSumDivisibleBy_postcond (n : Nat) (d : Nat) (result: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Prop :=
  -- !benchmark @start postcond
  (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n))) - result = 0 ∧
  result ≤ (List.length (List.filter (fun x => x < n ∧ (sumOfDigits x) % d = 0) (List.range n)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countSumDivisibleBy_spec_satisfied (n: Nat) (d: Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    countSumDivisibleBy_postcond (n) (d) (countSumDivisibleBy (n) (d) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_9
