import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashSet
open Std
-- !benchmark @end import

namespace verina_advanced_28


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestConsecutive_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longestConsecutive (nums : List Int) (h_precond : longestConsecutive_precond (nums)) : Nat :=
  -- !benchmark @start code
  Id.run do
    let mut set := HashSet.empty
    for x in nums do
      set := set.insert x

    let mut maxLen := 0

    for x in nums do
      if !set.contains (x - 1) then
        let mut curr := x
        let mut length := 1
        while set.contains (curr + 1) do
          curr := curr + 1
          length := length + 1
        maxLen := Nat.max maxLen length

    return maxLen
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def isConsecutive (seq : List Int) : Bool :=
  seq.length = 0 ∨ seq.zipIdx.all (fun (x, i) => x = i + seq[0]!)
-- !benchmark @end postcond_aux


@[reducible, simp]
def longestConsecutive_postcond (nums : List Int) (result: Nat) (h_precond : longestConsecutive_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let sorted_nums := nums.mergeSort
  let consec_sublist_lens := List.range nums.length |>.flatMap (fun start =>
    List.range (nums.length - start + 1) |>.map (fun len => sorted_nums.extract start (start + len))) |>.filter isConsecutive |>.map (·.length)

  (nums = [] → result = 0) ∧
  (nums ≠ [] → consec_sublist_lens.contains result ∧ consec_sublist_lens.all (· ≤ result))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestConsecutive_spec_satisfied (nums: List Int) (h_precond : longestConsecutive_precond (nums)) :
    longestConsecutive_postcond (nums) (longestConsecutive (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_28
