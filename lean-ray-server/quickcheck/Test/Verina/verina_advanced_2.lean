import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_2


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def intMax (x y : Int) : Int :=
  if x < y then y else x
-- !benchmark @end code_aux


def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  -- !benchmark @start code
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (m + 1) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible, simp]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

set_option trace.quickcheck true in
theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  -- Note: removed unfold to test complexity analysis detection
  unfold LongestCommonSubsequence_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true })

  -- !benchmark @end proof
end verina_advanced_2
