import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_57


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def nextGreaterElement_precond (nums1 : List Int) (nums2 : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums1 ∧
  List.Nodup nums2 ∧
  nums1.all (fun x => x ∈ nums2)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def nextGreaterElement (nums1 : List Int) (nums2 : List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : List Int :=
  -- !benchmark @start code
  let len1 := nums1.length

  let buildNextGreaterMap : List (Int × Int) :=
    let rec mapLoop (index : Nat) (stack : List Nat) (map : List (Int × Int)) : List (Int × Int) :=
      if h : index >= nums2.length then
        stack.foldl (fun acc pos => (nums2[pos]!, -1) :: acc) map
      else
        let currentValue := nums2[index]!

        let rec processStack (s : List Nat) (m : List (Int × Int)) : List Nat × List (Int × Int) :=
          match s with
          | [] => ([], m)
          | topIndex :: rest =>
              let topValue := nums2[topIndex]!
              if currentValue > topValue then
                let newMap := (topValue, currentValue) :: m
                processStack rest newMap
              else
                (s, m)

        let (newStack, newMap) := processStack stack map

        mapLoop (index + 1) (index :: newStack) newMap
      termination_by nums2.length - index

    mapLoop 0 [] []

  let buildResult : List Int :=
    let rec resultLoop (i : Nat) (result : List Int) : List Int :=
      if i >= len1 then
        result.reverse
      else
        let val := nums1[i]!
        let rec findInMap (m : List (Int × Int)) : Int :=
          match m with
          | [] => -1
          | (num, nextGreater) :: rest =>
              if num == val then nextGreater
              else findInMap rest

        let nextGreater := findInMap buildNextGreaterMap
        resultLoop (i + 1) (nextGreater :: result)
      termination_by len1 - i

    resultLoop 0 []

  buildResult
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def nextGreaterElement_postcond (nums1 : List Int) (nums2 : List Int) (result: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) : Prop :=
  -- !benchmark @start postcond
  result.length = nums1.length ∧

  (List.range nums1.length |>.all (fun i =>
    let val := nums1[i]!
    let resultVal := result[i]!

    let j := nums2.findIdx? (fun x => x == val)
    match j with
    | none => false
    | some idx =>
      let nextGreater := (List.range (nums2.length - idx - 1)).find? (fun k =>
        let pos := idx + k + 1
        nums2[pos]! > val
      )

      match nextGreater with
      | none => resultVal = -1
      | some offset => resultVal = nums2[idx + offset + 1]!
  )) ∧
  (result.all (fun val =>
    val = -1 ∨ val ∈ nums2
  ))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem nextGreaterElement_spec_satisfied (nums1: List Int) (nums2: List Int) (h_precond : nextGreaterElement_precond (nums1) (nums2)) :
    nextGreaterElement_postcond (nums1) (nums2) (nextGreaterElement (nums1) (nums2) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_57
