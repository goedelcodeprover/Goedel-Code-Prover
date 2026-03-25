import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_77


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  -- !benchmark @start precond
  index1 < arr.size ∧
  ((h : index1 < arr.size) → index2 < (arr[index1]'h).size)
  -- !benchmark @end precond


-- !benchmark @start code_aux
def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val
-- !benchmark @end code_aux


def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  -- !benchmark @start code
  let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def modify_array_element_postcond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (result: Array (Array Nat)) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :=
  -- !benchmark @start postcond
  (∀ i, i < arr.size → i ≠ index1 → result[i]! = arr[i]!)
  ∧
  (∀ j, j < (arr[index1]!).size → j ≠ index2 → (result[index1]!)[j]! = (arr[index1]!)[j]!) ∧
  ((result[index1]!)[index2]! = val)
  -- !benchmark @end postcond


-- set_option trace.quickcheck.adaptive true in
-- set_option trace.quickcheck.preprocess true in
set_option trace.quickcheck true in
theorem modify_array_element_spec_satisfied (arr: Array (Array Nat)) (index1: Nat) (index2: Nat) (val: Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    modify_array_element_postcond (arr) (index1) (index2) (val) (modify_array_element (arr) (index1) (index2) (val) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold modify_array_element_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true })

  -- !benchmark @end proof

end verina_basic_77
