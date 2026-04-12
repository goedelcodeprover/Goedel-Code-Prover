import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Tactic
import Tacs
set_option maxHeartbeats 0

namespace LeetCode_test_problems_leetcode_2731

-- Modulus constant (must be defined before use)
def MOD : Nat := 1000000007

-- Precondition definitions
@[reducible, simp]
def sumRobotPairDistances_precond (nums : List Int) (s : String) (d : Nat) : Prop :=
  -- !benchmark @start precond
  nums.length = s.length ∧
    2 ≤ nums.length ∧
    (∀ i, i < nums.length → Int.natAbs (nums[i]!) ≤ 2000000000) ∧
    nums.Nodup
  -- !benchmark @end precond


-- Main function definitions
def sumRobotPairDistances (nums : List Int) (s : String) (d : Nat)
    (h_precond : sumRobotPairDistances_precond nums s d) : Nat :=
  -- !benchmark @start code
  let chars : List Char := s.data
  -- compute final positions after d seconds assuming robots pass through each other
  let pos : List Int :=
    (List.range nums.length).map fun i =>
      let dir : Int := if chars[i]! = 'R' then (1 : Int) else (-1)
      nums[i]! + (Int.ofNat d) * dir
  -- sum pairwise distances modulo MOD as specified in the postcondition
  (List.range nums.length).foldl
    (fun acc i =>
      (List.range nums.length).foldl
        (fun acc' j =>
          if i < j then
            acc' + Nat.mod (Int.natAbs (pos[i]! - pos[j]!)) MOD
          else acc')
        acc)
    0
  -- !benchmark @end code


-- Postcondition auxiliary definitions
opaque finalPos (nums : List Int) (s : String) (d : Nat) : List Int

-- Postcondition definitions
@[reducible, simp]
def sumRobotPairDistances_postcond (nums : List Int) (s : String) (d : Nat)
    (result : Nat) (h_precond : sumRobotPairDistances_precond nums s d) : Prop :=
  -- !benchmark @start postcond
  let pos := finalPos nums s d
  pos.length = nums.length ∧
    result =
      ((List.range nums.length).foldl
          (fun acc i =>
            (List.range nums.length).foldl
              (fun acc' j =>
                if i < j then
                  acc' + Nat.mod (Int.natAbs (pos[i]! - pos[j]!)) MOD
                else acc')
              acc)
          0)
  -- !benchmark @end postcond


-- Proof content
theorem sumRobotPairDistances_postcond_satisfied (nums : List Int) (s : String) (d : Nat)
    (h_precond : sumRobotPairDistances_precond nums s d) :
    sumRobotPairDistances_postcond nums s d
      (sumRobotPairDistances nums s d h_precond) h_precond := by
  -- !benchmark @start proof
  -- countNodesAll
  -- !benchmark @end proof

end LeetCode_test_problems_leetcode_2731
