import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashMap
open Std
-- !benchmark @end import

namespace verina_advanced_29


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longestGoodSubarray (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let arr := nums.toArray
    let mut left := 0
    let mut maxLen := 0
    let mut freq : HashMap Nat Nat := {}

    for right in [0:arr.size] do
      let num := arr[right]!
      let count := freq.getD num 0
      freq := freq.insert num (count + 1)

      -- If any frequency > k, shrink the window from the left
      while freq.toList.any (fun (_, v) => v > k) do
        let lnum := arr[left]!
        let lcount := freq.getD lnum 0
        if lcount = 1 then
          freq := freq.erase lnum
        else
          freq := freq.insert lnum (lcount - 1)
        left := left + 1

      maxLen := max maxLen (right - left + 1)

    return maxLen
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def longestGoodSubarray_postcond (nums : List Nat) (k : Nat) (result: Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  let subArrays :=
    List.range (nums.length + 1) |>.flatMap (fun start =>
      List.range (nums.length - start + 1) |>.map (fun len =>
        nums.drop start |>.take len))
  let subArrayFreqs := subArrays.map (fun arr => arr.map (fun x => arr.count x))
  let validSubArrays := subArrayFreqs.filter (fun arr => arr.all (fun x => x ≤ k))

  (nums = [] ∧ result = 0) ∨
  (nums ≠ [] ∧
    validSubArrays.any (fun arr => arr.length = result) ∧
    validSubArrays.all (fun arr => arr.length ≤ result))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestGoodSubarray_spec_satisfied (nums: List Nat) (k: Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    longestGoodSubarray_postcond (nums) (k) (longestGoodSubarray (nums) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_29
