import Quickcheck

namespace verina_advanced_4


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestIncreasingSubsequence_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def intMax (x y : Int) : Int :=
  if x < y then y else x
-- !benchmark @end code_aux


def LongestIncreasingSubsequence (a : Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Int :=
  -- !benchmark @start code
  let n := a.size
  let dp := Id.run do
    let mut dp := Array.mkArray n 1
    for i in [1:n] do
      for j in [0:i] do
        if a[j]! < a[i]! then
          let newVal := intMax (dp[i]!) (dp[j]! + 1)
          dp := dp.set! i newVal
    return dp
  match dp with
  | #[] => 0
  | _   => dp.foldl intMax 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LongestIncreasingSubsequence_postcond (a : Array Int) (result: Int) (h_precond : LongestIncreasingSubsequence_precond (a)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (a.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LongestIncreasingSubsequence_spec_satisfied (a: Array Int) (h_precond : LongestIncreasingSubsequence_precond (a)) :
    LongestIncreasingSubsequence_postcond (a) (LongestIncreasingSubsequence (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold LongestIncreasingSubsequence_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_4
