import Quickcheck

namespace verina_advanced_32


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def longestIncreasingSubsequence (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  -- !benchmark @start code
  let rec buildTables : List Int → List Int → List Nat → Nat → Nat
    | [], _, lengths, _ =>
        let rec findMaxLength : List Nat → Nat
          | [] => 0
          | x :: xs =>
              let maxRest := findMaxLength xs
              if x > maxRest then x else maxRest
        findMaxLength lengths
    | currNum :: restNums, prevNums, lengths, idx =>
        let rec findLengthEndingAtCurr : List Int → List Nat → Nat → Nat
          | [], _, best => best
          | prevVal :: restVals, prevLen :: restLens, best =>
              if prevVal < currNum then
                findLengthEndingAtCurr restVals restLens (max best prevLen)
              else
                findLengthEndingAtCurr restVals restLens best
          | _, _, best => best

        let bestPrevLen := findLengthEndingAtCurr prevNums lengths 0
        let currLength := bestPrevLen + 1
        buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)

  match numbers with
  | [] => 0
  | [x] => 1
  | first :: rest => buildTables rest [first] [1] 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def longestIncreasingSubsequence_postcond (numbers : List Int) (result: Nat) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Prop :=
  -- !benchmark @start postcond
  let allSubseq := (numbers.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let increasingSubseqLens := allSubseq.filter (fun l => List.Pairwise (· < ·) l) |>.map (·.length)
  increasingSubseqLens.contains result ∧ increasingSubseqLens.all (· ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem longestIncreasingSubsequence_spec_satisfied (numbers: List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    longestIncreasingSubsequence_postcond (numbers) (longestIncreasingSubsequence (numbers) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_32
