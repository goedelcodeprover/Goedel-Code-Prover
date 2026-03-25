import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_60


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  -- !benchmark @start code
  let rec helper (nums : List Nat) : (List Nat × List Nat) :=
    match nums with
    | [] => ([], [])
    | x :: xs =>
      let (evens, odds) := helper xs
      if x % 2 == 0 then (x :: evens, odds)
      else (evens, x :: odds)
  helper nums
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  -- !benchmark @start postcond
  let evens := result.fst
  let odds := result.snd
  -- All elements from nums are in evens ++ odds, no extras
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem partitionEvensOdds_spec_satisfied (nums: List Nat) (h_precond : partitionEvensOdds_precond (nums)) :
    partitionEvensOdds_postcond (nums) (partitionEvensOdds (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_60
