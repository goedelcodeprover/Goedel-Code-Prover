import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_24


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Int :=
  -- !benchmark @start code
  let rec lisHelper (dp : List Int) (x : Int) : List Int :=
    let rec replace (l : List Int) (acc : List Int) : List Int :=
      match l with
      | [] => (acc.reverse ++ [x])
      | y :: ys => if x ≤ y then acc.reverse ++ (x :: ys) else replace ys (y :: acc)
    replace dp []

  let finalDP := nums.foldl lisHelper []
  finalDP.length
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lengthOfLIS_postcond (nums : List Int) (result: Int) (h_precond : lengthOfLIS_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  -- Helper function to check strictly increasing
  let rec isStrictlyIncreasing (l : List Int) : Bool :=
    match l with
    | [] | [_] => true
    | x :: y :: rest => x < y && isStrictlyIncreasing (y :: rest)

  -- Generate all subsequences
  let rec subsequences (xs : List Int) : List (List Int) :=
    match xs with
    | [] => [[]]
    | x :: xs' =>
      let rest := subsequences xs'
      rest ++ rest.map (fun r => x :: r)

  let allIncreasing := subsequences nums |>.filter (fun l => isStrictlyIncreasing l)

  allIncreasing.any (fun l => l.length = result) ∧
  allIncreasing.all (fun l => l.length ≤ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lengthOfLIS_spec_satisfied (nums: List Int) (h_precond : lengthOfLIS_precond (nums)) :
    lengthOfLIS_postcond (nums) (lengthOfLIS (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_24
