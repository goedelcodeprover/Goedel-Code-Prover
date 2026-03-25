import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_87


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a
-- !benchmark @end code_aux


def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  -- !benchmark @start code
  let indices := List.range a.size
  indices.foldl (fun arr i =>
    let minIdx := findMinIndexInRange arr i a.size
    swap arr i minIdx
  ) a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SelectionSort_postcond (a : Array Int) (result: Array Int) (h_precond : SelectionSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm a.toList result.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SelectionSort_spec_satisfied (a: Array Int) (h_precond : SelectionSort_precond (a)) :
    SelectionSort_postcond (a) (SelectionSort (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_87
