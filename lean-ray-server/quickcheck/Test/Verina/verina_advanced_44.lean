import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_44


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxSubarraySumDivisibleByK_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  k > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxSubarraySumDivisibleByK (arr : Array Int) (k : Int) : Int :=
  -- !benchmark @start code
  let n := arr.size
  if n = 0 || k = 0 then 0
  else
    --compute prefix sums for efficient subarray sum calculation
    let prefixSums := Id.run do
      let mut prefixSums := Array.mkArray (n + 1) 0
      for i in [0:n] do
        prefixSums := prefixSums.set! (i+1) (prefixSums[i]! + arr[i]!)
      prefixSums

    let minElem := Id.run do -- find minimum element
      let mut minElem := arr[0]!
      for elem in arr do
        minElem := min minElem elem
      minElem
    let maxSum := Id.run do
      let mut maxSum := minElem - 1
      --check all subarrays with length divisible by k
      for len in List.range (n+1) do
        if len % k = 0 && len > 0 then
          for start in [0:(n - len + 1)] do
            let endIdx := start + len
            let subarraySum := prefixSums[endIdx]! - prefixSums[start]!
            maxSum := max maxSum subarraySum
      maxSum

    let default : Int := minElem - 1
    if maxSum = default then 0 else maxSum
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxSubarraySumDivisibleByK_postcond (arr : Array Int) (k : Int) (result: Int) : Prop :=
  -- !benchmark @start postcond
  let subarrays := List.range (arr.size) |>.flatMap (fun start =>
    List.range (arr.size - start + 1) |>.map (fun len => arr.extract start (start + len)))
  let divisibleSubarrays := subarrays.filter (fun subarray => subarray.size % k = 0 && subarray.size > 0)
  let subarraySums := divisibleSubarrays.map (fun subarray => subarray.sum)
  (result = 0 → subarraySums.length = 0) ∧
  (result ≠ 0 → result ∈ subarraySums ∧ subarraySums.all (fun sum => sum ≤ result))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxSubarraySumDivisibleByK_spec_satisfied (arr: Array Int) (k: Int) :
    maxSubarraySumDivisibleByK_postcond (arr) (k) (maxSubarraySumDivisibleByK (arr) (k)) := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_44
