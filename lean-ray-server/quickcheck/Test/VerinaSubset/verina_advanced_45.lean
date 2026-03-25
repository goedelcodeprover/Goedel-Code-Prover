import Quickcheck
import Quickcheck.SplitTacs.SplitMatch

set_option maxHeartbeats 0

namespace verina_advanced_45

@[reducible, simp]
def maxSubarraySum_precond (xs : List Int) : Prop :=
  True

def maxSubarraySum (xs : List Int) (h_precond : maxSubarraySum_precond (xs)) : Int :=
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

@[reducible, simp]
def maxSubarraySum_postcond (xs : List Int) (result: Int) (h_precond : maxSubarraySum_precond (xs)) : Prop :=
  let subarray_sums := List.range (xs.length + 1) |>.flatMap (fun start =>
    List.range' 1 (xs.length - start) |>.map (fun len =>
      ((xs.drop start).take len).sum
    ))

  let has_result_subarray := subarray_sums.any (fun sum => sum == result)


  let is_maximum := subarray_sums.all (· ≤ result)

  match xs with
  | [] => result == 0
  | _ => has_result_subarray ∧ is_maximum

theorem maxSubarraySum_spec_satisfied (xs: List Int) (h_precond : maxSubarraySum_precond (xs)) :
    maxSubarraySum_postcond (xs) (maxSubarraySum (xs) h_precond) h_precond := by
    unfold maxSubarraySum_precond at h_precond
    unfold maxSubarraySum_postcond
    quickcheck (config := { Quickcheck.Configuration.normal with quiet := true, randomSeed := some 42 })

#eval maxSubarraySum [-4, -4, -5] (by simp [maxSubarraySum_precond])
#eval maxSubarraySum_postcond [-4, -4, -5] (maxSubarraySum [-4, -4, -5] (by simp [maxSubarraySum_precond])) (by simp [maxSubarraySum_precond])

end verina_advanced_45
