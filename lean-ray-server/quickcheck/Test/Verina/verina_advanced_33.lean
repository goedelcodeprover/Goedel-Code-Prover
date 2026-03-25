import Quickcheck

namespace verina_advanced_33


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  -- !benchmark @start code
  let max2 (a : Nat) (b : Nat) : Nat :=
    if a > b then a else b

  let rec listLength (l : List Int) : Nat :=
    match l with
    | []      => 0
    | _ :: xs => 1 + listLength xs

  let rec helper (lst : List Int) (prev : Option Int) : Nat :=
    match lst with
    | [] => 0
    | h :: t =>
        let canTake : Bool :=
          if prev = none then true
          else if prev.get! < h then true else false
        let withTake : Nat :=
          if canTake then 1 + helper t (some h) else 0
        let withoutTake : Nat := helper t prev
        max2 withTake withoutTake

  let result := helper nums none
  result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def longestIncreasingSubsequence_postcond (nums : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (nums.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

set_option maxHeartbeats 0
theorem longestIncreasingSubsequence_spec_satisfied (nums: List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    longestIncreasingSubsequence_postcond (nums) (longestIncreasingSubsequence (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold longestIncreasingSubsequence_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_33
