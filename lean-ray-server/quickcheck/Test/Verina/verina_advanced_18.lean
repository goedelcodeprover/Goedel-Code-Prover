import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_18


-- !benchmark @start solution_aux
def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0
-- !benchmark @end code_aux


def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  -- !benchmark @start code
  let k := countDigits n
  sumPowers n k = n
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def isArmstrong_postcond (n : Nat) (result: Bool) (h_precond : isArmstrong_precond (n)) : Prop :=
  -- !benchmark @start postcond
  let n' := List.foldl (fun acc d => acc + d ^ countDigits n) 0 (List.map (fun c => c.toNat - '0'.toNat) (toString n).toList)
  (result → (n = n')) ∧
  (¬ result → (n ≠ n'))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isArmstrong_spec_satisfied (n: Nat) (h_precond : isArmstrong_precond (n)) :
    isArmstrong_postcond (n) (isArmstrong (n) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_18
