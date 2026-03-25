import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_37


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def majorityElement_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def majorityElement (nums : List Int) (h_precond : majorityElement_precond (nums)) : Int :=
  -- !benchmark @start code
  let rec insert (x : Int) (xs : List Int) : List Int :=
    match xs with
    | [] => [x]
    | h :: t =>
      if x ≤ h then
        x :: h :: t
      else
        h :: insert x t

  let rec insertionSort (xs : List Int) : List Int :=
    match xs with
    | [] => []
    | h :: t =>
      let sortedTail := insertionSort t
      let sorted := insert h sortedTail
      sorted

  let getAt := fun (xs : List Int) (i : Nat) =>
    match xs.drop i with
    | [] => 0
    | h :: _ => h

  let sorted := insertionSort nums

  let len := sorted.length
  let mid := len / 2
  getAt sorted mid
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def majorityElement_postcond (nums : List Int) (result: Int) (h_precond : majorityElement_precond (nums)) : Prop :=
  -- !benchmark @start postcond
  let n := nums.length
  (List.count result nums > n / 2) ∧
  nums.all (fun x => x = result ∨ List.count x nums ≤ n / 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem majorityElement_spec_satisfied (nums: List Int) (h_precond : majorityElement_precond (nums)) :
    majorityElement_postcond (nums) (majorityElement (nums) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_37
