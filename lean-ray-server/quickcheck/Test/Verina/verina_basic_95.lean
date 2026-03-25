import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_95


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def swap_precond (arr : Array Int) (i : Int) (j : Int) : Prop :=
  -- !benchmark @start precond
  i ≥ 0 ∧
  j ≥ 0 ∧
  Int.toNat i < arr.size ∧
  Int.toNat j < arr.size
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def swap (arr : Array Int) (i : Int) (j : Int) (h_precond : swap_precond (arr) (i) (j)) : Array Int :=
  -- !benchmark @start code
  let i_nat := Int.toNat i
  let j_nat := Int.toNat j
  let arr1 := arr.set! i_nat (arr[j_nat]!)
  let arr2 := arr1.set! j_nat (arr[i_nat]!)
  arr2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def swap_postcond (arr : Array Int) (i : Int) (j : Int) (result: Array Int) (h_precond : swap_precond (arr) (i) (j)) :=
  -- !benchmark @start postcond
  (result[Int.toNat i]! = arr[Int.toNat j]!) ∧
  (result[Int.toNat j]! = arr[Int.toNat i]!) ∧
  (∀ (k : Nat), k < arr.size → k ≠ Int.toNat i → k ≠ Int.toNat j → result[k]! = arr[k]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem swap_spec_satisfied (arr: Array Int) (i: Int) (j: Int) (h_precond : swap_precond (arr) (i) (j)) :
    swap_postcond (arr) (i) (j) (swap (arr) (i) (j) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_95
