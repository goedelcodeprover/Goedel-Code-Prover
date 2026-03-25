import Quickcheck

namespace verina_advanced_34


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  -- !benchmark @start code
  Id.run do
    if nums.isEmpty then return 0
    let mut sub : Array Int := Array.empty
    sub := sub.push nums.head!
    for num in nums.tail do
      if num > sub[sub.size - 1]! then
        sub := sub.push num
      else
       -- << binary search >>
        let mut left : Nat := 0
        let mut right : Nat := sub.size - 1
        while left < right do
          let mid := (left + right) / 2
          if sub[mid]! == num then
            right := mid
          else if sub[mid]! < num then
            left := mid + 1
          else
            right := mid
        sub := sub.set! left num
    return Int.ofNat sub.size
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_34
