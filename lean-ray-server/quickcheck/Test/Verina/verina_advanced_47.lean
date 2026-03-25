import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_47


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def mergeIntervals (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : List (Prod Int Int) :=
  -- !benchmark @start code
  -- Insertion sort based on the start of intervals
  let rec insert (x : Prod Int Int) (sorted : List (Prod Int Int)) : List (Prod Int Int) :=
    match sorted with
    | [] => [x]
    | y :: ys => if x.fst ≤ y.fst then x :: sorted else y :: insert x ys

  let rec sort (xs : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs with
    | [] => []
    | x :: xs' => insert x (sort xs')

  let sorted := sort intervals

  -- Merge sorted intervals
  let rec merge (xs : List (Prod Int Int)) (acc : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs, acc with
    | [], _ => acc.reverse
    | (s, e) :: rest, [] => merge rest [(s, e)]
    | (s, e) :: rest, (ps, pe) :: accTail =>
      if s ≤ pe then
        merge rest ((ps, max pe e) :: accTail)
      else
        merge rest ((s, e) :: (ps, pe) :: accTail)

  merge sorted []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def mergeIntervals_postcond (intervals : List (Prod Int Int)) (result: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : Prop :=
  -- !benchmark @start postcond
  -- Check that all original intervals are covered by some result interval
  let covered := intervals.all (fun (s, e) =>
    result.any (fun (rs, re) => rs ≤ s ∧ e ≤ re))

  -- Check that no intervals in the result overlap
  let rec noOverlap (l : List (Prod Int Int)) : Bool :=
    match l with
    | [] | [_] => true
    | (_, e1) :: (s2, e2) :: rest => e1 < s2 && noOverlap ((s2, e2) :: rest)

  covered ∧ noOverlap result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem mergeIntervals_spec_satisfied (intervals: List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    mergeIntervals_postcond (intervals) (mergeIntervals (intervals) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_47
