import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_77


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def trapRainWater_precond (height : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def trapRainWater (height : List Nat) (h_precond : trapRainWater_precond (height)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut left := 0
    let mut right := height.length - 1
    let mut leftMax := 0
    let mut rightMax := 0
    let mut water := 0

    while left < right do
      let hLeft := height[left]!
      let hRight := height[right]!

      if hLeft < hRight then
        if hLeft >= leftMax then
          leftMax := hLeft
        else
          water := water + (leftMax - hLeft)
        left := left + 1
      else
        if hRight >= rightMax then
          rightMax := hRight
        else
          water := water + (rightMax - hRight)
        right := right - 1

    return water
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def trapRainWater_postcond (height : List Nat) (result: Nat) (h_precond : trapRainWater_precond (height)) : Prop :=
  -- !benchmark @start postcond
  let waterAt := List.range height.length |>.map (fun i =>
    let lmax := List.take (i+1) height |>.foldl Nat.max 0
    let rmax := List.drop i height |>.foldl Nat.max 0
    Nat.min lmax rmax - height[i]!)

  result - (waterAt.foldl (· + ·) 0) = 0 ∧ (waterAt.foldl (· + ·) 0) ≤ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem trapRainWater_spec_satisfied (height: List Nat) (h_precond : trapRainWater_precond (height)) :
    trapRainWater_postcond (height) (trapRainWater (height) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_77
