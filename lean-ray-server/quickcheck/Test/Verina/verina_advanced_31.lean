import Quickcheck

namespace verina_advanced_31


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingSubseqLength_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Generate all subsequences
def subsequences {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    let subs := subsequences xs
    subs ++ subs.map (fun s => x :: s)

-- Check if a list is strictly increasing
def isStrictlyIncreasing : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => if x < y then isStrictlyIncreasing (y :: rest) else false
-- !benchmark @end code_aux


def longestIncreasingSubseqLength (xs : List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Nat :=
  -- !benchmark @start code
  let subs := subsequences xs
  let increasing := subs.filter isStrictlyIncreasing
  increasing.foldl (fun acc s => max acc s.length) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def longestIncreasingSubseqLength_postcond (xs : List Int) (result: Nat) (h_precond : longestIncreasingSubseqLength_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (xs.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestIncreasingSubseqLength_spec_satisfied (xs: List Int) (h_precond : longestIncreasingSubseqLength_precond (xs)) :
    longestIncreasingSubseqLength_postcond (xs) (longestIncreasingSubseqLength (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold longestIncreasingSubseqLength_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_31
