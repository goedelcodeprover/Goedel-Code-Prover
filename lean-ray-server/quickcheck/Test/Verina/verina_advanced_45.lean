import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_45


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxSubarraySum_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
  -- !benchmark @start code
  let rec helper (lst : List Int) (curMax : Int) (globalMax : Int) : Int :=
    match lst with
    | [] => globalMax
    | x :: rest =>
      let newCurMax := max x (curMax + x)
      let newGlobal := max globalMax newCurMax
      helper rest newCurMax newGlobal
  match xs with
  | [] => 0
  | x :: rest => helper rest x x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def maxSubarraySum_postcond (xs : List Int) (result: Int) (h_precond : maxSubarraySum_precond (xs)) : Prop :=
  -- !benchmark @start postcond
  -- Find all possible subarrays and their sums
  let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start =>
    List.range' 1 (xs.length - start) |>.map (fun len =>
      ((xs.drop start).take len).sum
    ))

  -- Check if there exists a subarray with sum equal to result
  let has_result_subarray := subarray_sums.any (fun sum => sum == result)


  -- Check if result is the maximum among all subarray sums
  let is_maximum := subarray_sums.all (· ≤ result)

  match xs with
  | [] => result == 0
  | _ => has_result_subarray ∧ is_maximum
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxSubarraySum_spec_satisfied (xs: List Int) (h_precond : maxSubarraySum_precond (xs)) :
    maxSubarraySum_postcond (xs) (maxSubarraySum (xs) h_precond) h_precond := by
  -- !benchmark @start proof
  -- Postcond is too complex: unfold causes whnf timeout (200k heartbeats)
  -- Cannot use onlyDecidable with such complex specifications
  sorry

  -- !benchmark @end proof
end verina_advanced_45
