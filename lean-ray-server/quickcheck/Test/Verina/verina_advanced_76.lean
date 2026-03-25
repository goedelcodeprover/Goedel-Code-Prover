import Quickcheck
-- !benchmark @start import type=solution
import Std
open Std
-- !benchmark @end import

namespace verina_advanced_76


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ nums.eraseDups.length
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  -- !benchmark @start code
  let freqMap : HashMap Int Nat :=
    nums.foldl (init := {}) fun acc n =>
      let oldVal := match acc.toList.find? (fun (key, _) => key == n) with
                    | some (_, c) => c
                    | none        => 0
      acc.insert n (oldVal + 1)
  let sorted := freqMap.toList.foldl
    (fun acc pair =>
      let (x, cx) := pair
      let rec insertSorted (xs : List (Int × Nat)) : List (Int × Nat) :=
        match xs with
        | [] => [pair]
        | (y, cy) :: ys =>
          if cx > cy then
            pair :: (y, cy) :: ys
          else
            (y, cy) :: insertSorted ys
      insertSorted acc
    ) []

  sorted.take k |>.map (fun (n, _) => n)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- Key optimization lemma: turn nested `all` quantifiers into checking only elements not in `result`.
-- This greatly reduces how many elements must be checked (from all of `nums` to `nums.filter (· ∉ result)`).
-- Tag with @[quickcheck] so SafeNorm can apply this lemma automatically.
-- @[simp, quickcheck]
-- theorem all_nested_optimize (nums result : List Int) :
--     (result.all (fun x =>
--       nums.all (fun y =>
--         y ∉ result →
--           nums.count x > nums.count y ∨
--           (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
--       ))) =
--     (result.all (fun x =>
--       (nums.filter (· ∉ result)).all (fun y =>
--         nums.count x > nums.count y ∨
--         (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
--       ))) := by
--   sorry  -- Lemma proof: the two expressions are logically equivalent because `filter` keeps only elements not in `result`.

-- !benchmark @end postcond_aux


@[reducible]
def topKFrequent_postcond (nums : List Int) (k : Nat) (result: List Int) (h_precond : topKFrequent_precond (nums) (k)) : Prop :=
  -- !benchmark @start postcond
  -- Result contains exactly k elements
  result.length = k ∧

  -- All elements in result appear in the original list
  result.all (· ∈ nums) ∧

  -- All elements in result are distinct
  List.Pairwise (· ≠ ·) result ∧

  -- For any element in result and any element not in result, the frequency of the
  -- element in result is greater or equal
  (result.all (fun x =>
    nums.all (fun y =>
      y ∉ result →
        nums.count x > nums.count y ∨
        (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
    ))) ∧

  -- Elements in result are ordered by decreasing frequency
  List.Pairwise (fun (x, i) (y, j) =>
    i < j → nums.count x > nums.count y ∨
    (nums.count x == nums.count y ∧ nums.idxOf x < nums.idxOf y)
  ) result.zipIdx
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.safenorm true
theorem topKFrequent_spec_satisfied (nums: List Int) (k: Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    topKFrequent_postcond (nums) (k) (topKFrequent (nums) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold topKFrequent_postcond topKFrequent
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- apply And.intro
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- apply And.intro
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- apply And.intro
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- apply And.intro
  -- sorry
  -- -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })



  -- !benchmark @end proof
end verina_advanced_76
