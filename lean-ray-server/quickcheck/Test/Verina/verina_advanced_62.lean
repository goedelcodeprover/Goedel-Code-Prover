import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_62


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def rain_precond (heights : List (Int)) : Prop :=
  -- !benchmark @start precond
  heights.all (fun h => h >= 0)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def rain (heights : List (Int)) (h_precond : rain_precond (heights)) : Int :=
  -- !benchmark @start code
  -- Handle edge cases: need at least 3 elements to trap water
  if heights.length < 3 then 0 else
    let n := heights.length

    -- Use two pointers approach for O(n) time with O(1) space
    let rec aux (left : Nat) (right : Nat) (leftMax : Int) (rightMax : Int) (water : Int) : Int :=
      if left >= right then
        water  -- Base case: all elements processed
      else if heights[left]! <= heights[right]! then
        -- Process from the left
        let newLeftMax := max leftMax (heights[left]!)
        let newWater := water + max 0 (leftMax - heights[left]!)
        aux (left+1) right newLeftMax rightMax newWater
      else
        -- Process from the right
        let newRightMax := max rightMax (heights[right]!)
        let newWater := water + max 0 (rightMax - heights[right]!)
        aux left (right-1) leftMax newRightMax newWater
      termination_by right - left
    -- Initialize with two pointers at the ends
    aux 0 (n-1) (heights[0]!) (heights[n-1]!) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def rain_postcond (heights : List (Int)) (result: Int) (h_precond : rain_precond (heights)) : Prop :=
  -- !benchmark @start postcond
  -- The result is the total amount of rainwater trapped by the given terrain
  -- If there are fewer than 3 elements, no water can be trapped
  result >= 0 ∧
  -- The result is non-negative
  if heights.length < 3 then result = 0 else
    -- Water trapped at each position is min(maxLeft, maxRight) - height
    result =
      let max_left_at := λ i =>
        let rec ml (j : Nat) (max_so_far : Int) : Int :=
          if j > i then max_so_far
          else ml (j+1) (max max_so_far (heights[j]!))
          termination_by i + 1 - j
        ml 0 0

      let max_right_at := λ i =>
        let rec mr (j : Nat) (max_so_far : Int) : Int :=
          if j >= heights.length then max_so_far
          else mr (j+1) (max max_so_far (heights[j]!))
          termination_by heights.length - j
        mr i 0

      let water_at := λ i =>
        max 0 (min (max_left_at i) (max_right_at i) - heights[i]!)

      let rec sum_water (i : Nat) (acc : Int) : Int :=
        if i >= heights.length then acc
        else sum_water (i+1) (acc + water_at i)
        termination_by heights.length - i

      sum_water 0 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rain_spec_satisfied (heights: List (Int)) (h_precond : rain_precond (heights)) :
    rain_postcond (heights) (rain (heights) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_62
