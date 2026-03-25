import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_42


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxProfit_precond (prices : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit
-- !benchmark @end code_aux


def maxProfit (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  -- !benchmark @start code
  match prices with
  | [] => 0
  | p :: ps => maxProfitAux ps p 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxProfit_postcond (prices : List Nat) (result: Nat) (h_precond : maxProfit_precond (prices)) : Prop :=
  -- !benchmark @start postcond
  (result = 0 ∧ prices = []) ∨
  (
    -- All valid transactions have profit ≤ result (using pairwise)
    List.Pairwise (fun ⟨pi, i⟩ ⟨pj, j⟩ => i < j → pj - pi ≤ result) prices.zipIdx ∧

    -- There exists a transaction with profit = result (using any)
    prices.zipIdx.any (fun ⟨pi, i⟩ =>
      prices.zipIdx.any (fun ⟨pj, j⟩ =>
        i < j ∧ pj - pi = result))
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxProfit_spec_satisfied (prices: List Nat) (h_precond : maxProfit_precond (prices)) :
    maxProfit_postcond (prices) (maxProfit (prices) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_42
