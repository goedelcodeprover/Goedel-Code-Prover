import Quickcheck

namespace verina_advanced_25


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0
-- !benchmark @end code_aux


def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  -- !benchmark @start code
  if nums.isEmpty then 0
  else
    let n := nums.length
    Id.run do
      let mut dp : Array Nat := Array.mkArray n 1

      for i in [1:n] do
        for j in [0:i] do
          if nums[j]! < nums[i]! && dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (dp[j]! + 1)

      maxInArray dp
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def lengthOfLIS_postcond (nums : List Int) (result: Nat) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond

-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lengthOfLIS_spec_satisfied (nums: List Int) (h_precond : lengthOfLIS_precond (nums)) :
    lengthOfLIS_postcond (nums) (lengthOfLIS (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold lengthOfLIS_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_25
