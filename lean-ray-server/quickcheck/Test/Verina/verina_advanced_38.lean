import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_38


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  -- !benchmark @start precond
  intervals.length > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxCoverageAfterRemovingOne (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Nat :=
  -- !benchmark @start code
  let n := intervals.length
  if n ≤ 1 then 0
  else
    (List.range n).foldl (fun acc i =>
      let remaining := List.eraseIdx intervals i
      let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged := sorted.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let coverage := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      max acc coverage
    ) 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxCoverageAfterRemovingOne_postcond (intervals : List (Prod Nat Nat)) (result: Nat) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Prop :=
  -- !benchmark @start postcond
  ∃ i < intervals.length,
    let remaining := List.eraseIdx intervals i
    let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
    let merged := sorted.foldl (fun acc curr =>
      match acc with
      | [] => [curr]
      | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
    ) []
    let cov := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
    result = cov ∧
    ∀ j < intervals.length,
      let rem_j := List.eraseIdx intervals j
      let sort_j := List.mergeSort rem_j (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged_j := sort_j.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let cov_j := merged_j.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      cov ≥ cov_j
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxCoverageAfterRemovingOne_spec_satisfied (intervals: List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    maxCoverageAfterRemovingOne_postcond (intervals) (maxCoverageAfterRemovingOne (intervals) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_38
