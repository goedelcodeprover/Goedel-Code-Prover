import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_8


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def canCompleteCircuit (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Int :=
  -- !benchmark @start code
  let totalGas := gas.foldl (· + ·) 0
  let totalCost := cost.foldl (· + ·) 0

  if totalGas < totalCost then
    -1
  else
    let rec loop (g c : List Int) (idx : Nat) (tank : Int) (start : Nat) : Int :=
      match g, c with
      | [], [] => start
      | gi :: gs, ci :: cs =>
        let tank' := tank + gi - ci
        if tank' < 0 then
          loop gs cs (idx + 1) 0 (idx + 1)
        else
          loop gs cs (idx + 1) tank' start
      | _, _ => -1  -- lengths don’t match

    let zipped := List.zip gas cost
    let rec walk (pairs : List (Int × Int)) (i : Nat) (tank : Int) (start : Nat) : Int :=
      match pairs with
      | [] => start
      | (g, c) :: rest =>
        let newTank := tank + g - c
        if newTank < 0 then
          walk rest (i + 1) 0 (i + 1)
        else
          walk rest (i + 1) newTank start

    walk zipped 0 0 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def canCompleteCircuit_postcond (gas : List Int) (cost : List Int) (result: Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Prop :=
  -- !benchmark @start postcond
  let valid (start : Nat) := List.range gas.length |>.all (fun i =>
    let acc := List.range (i + 1) |>.foldl (fun t j =>
      let jdx := (start + j) % gas.length
      t + gas[jdx]! - cost[jdx]!) 0
    acc ≥ 0)
  -- For result = -1: It's impossible to complete the circuit starting from any index
  -- In other words, there's no starting point from which we can always maintain a non-negative gas tank
  (result = -1 → (List.range gas.length).all (fun start => ¬ valid start)) ∧
  -- For result ≥ 0: This is the valid starting point
  -- When starting from this index, the gas tank never becomes negative during the entire circuit
  (result ≥ 0 → result < gas.length ∧ valid result.toNat ∧ (List.range result.toNat).all (fun start => ¬ valid start))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem canCompleteCircuit_spec_satisfied (gas: List Int) (cost: List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    canCompleteCircuit_postcond (gas) (cost) (canCompleteCircuit (gas) (cost) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_8
