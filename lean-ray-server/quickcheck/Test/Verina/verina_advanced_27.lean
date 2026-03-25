import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_27


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestCommonSubsequence_precond (s1 : String) (s2 : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
partial def toCharList (s : String) : List Char :=
  s.data

partial def fromCharList (cs : List Char) : String :=
  cs.foldl (fun acc c => acc.push c) ""

partial def lcsAux (xs : List Char) (ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' =>
    if x == y then
      x :: lcsAux xs' ys'
    else
      let left  := lcsAux xs' (y :: ys')
      let right := lcsAux (x :: xs') ys'
      if left.length >= right.length then left else right
-- !benchmark @end code_aux


def longestCommonSubsequence (s1 : String) (s2 : String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : String :=
  -- !benchmark @start code
  let xs := toCharList s1
  let ys := toCharList s2
  let resultList := lcsAux xs ys
  fromCharList resultList
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def longestCommonSubsequence_postcond (s1 : String) (s2 : String) (result: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq (arr : List Char) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq s1.toList
  let subseqB := allSubseq s2.toList
  let commonSubseq := subseqA.filter (fun l => subseqB.contains l)
  commonSubseq.contains result.toList ∧ commonSubseq.all (fun l => l.length ≤ result.length)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestCommonSubsequence_spec_satisfied (s1: String) (s2: String) (h_precond : longestCommonSubsequence_precond (s1) (s2)) :
    longestCommonSubsequence_postcond (s1) (s2) (longestCommonSubsequence (s1) (s2) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_27
