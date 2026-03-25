import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_81


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def uniqueSorted_precond (arr : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def uniqueSorted (arr : List Int) (h_precond : uniqueSorted_precond (arr)) : List Int :=
  -- !benchmark @start code
  let rec insert (x : Int) (sorted : List Int) : List Int :=
  match sorted with
  | [] =>
    [x]
  | head :: tail =>
    if x <= head then
      x :: head :: tail
    else
      head :: insert x tail

let rec insertionSort (xs : List Int) : List Int :=
  match xs with
  | [] =>
    []
  | h :: t =>
    let sortedTail := insertionSort t
    insert h sortedTail

let removeDups : List Int → List Int
| xs =>
  let rec aux (remaining : List Int) (seen : List Int) (acc : List Int) : List Int :=
    match remaining with
    | [] =>
      acc.reverse
    | h :: t =>
      if h ∈ seen then
        aux t seen acc
      else
        aux t (h :: seen) (h :: acc)
  aux xs [] []

insertionSort (removeDups arr)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def uniqueSorted_postcond (arr : List Int) (result: List Int) (h_precond : uniqueSorted_precond (arr)) : Prop :=
  -- !benchmark @start postcond
  List.isPerm arr.eraseDups result ∧ List.Pairwise (· ≤ ·) result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem uniqueSorted_spec_satisfied (arr: List Int) (h_precond : uniqueSorted_precond (arr)) :
    uniqueSorted_postcond (arr) (uniqueSorted (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_81
