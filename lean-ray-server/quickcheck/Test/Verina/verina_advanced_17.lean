import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_17


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def insertionSort_precond (l : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- Helper function to insert an integer into a sorted list
def insertElement (x : Int) (l : List Int) : List Int :=
  match l with
  | [] => [x]
  | y :: ys =>
      if x <= y then
        x :: y :: ys
      else
        y :: insertElement x ys

-- Helper function to sort a list using insertion sort
def sortList (l : List Int) : List Int :=
  match l with
  | [] => []
  | x :: xs =>
      insertElement x (sortList xs)
-- !benchmark @end code_aux


def insertionSort (l : List Int) (h_precond : insertionSort_precond (l)) : List Int :=
  -- !benchmark @start code
  let result := sortList l
  result
  -- !benchmark @end code


-- !benchmark @start postcond_aux
-- !benchmark @end postcond_aux


@[reducible]
def insertionSort_postcond (l : List Int) (result: List Int) (h_precond : insertionSort_precond (l)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result ∧ List.isPerm l result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem insertionSort_spec_satisfied (l: List Int) (h_precond : insertionSort_precond (l)) :
    insertionSort_postcond (l) (insertionSort (l) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_17
