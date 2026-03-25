import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_84


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def replace_precond (arr : Array Int) (k : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def replace_loop (oldArr : Array Int) (k : Int) : Nat → Array Int → Array Int
| i, acc =>
  if i < oldArr.size then
    if (oldArr[i]!) > k then
      replace_loop oldArr k (i+1) (acc.set! i (-1))
    else
      replace_loop oldArr k (i+1) acc
  else
    acc
-- !benchmark @end code_aux


def replace (arr : Array Int) (k : Int) (h_precond : replace_precond (arr) (k)) : Array Int :=
  -- !benchmark @start code
  replace_loop arr k 0 arr
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def replace_postcond (arr : Array Int) (k : Int) (result: Array Int) (h_precond : replace_precond (arr) (k)) :=
  -- !benchmark @start postcond
  (∀ i : Nat, i < arr.size → (arr[i]! > k → result[i]! = -1)) ∧
  (∀ i : Nat, i < arr.size → (arr[i]! ≤ k → result[i]! = arr[i]!))
  -- !benchmark @end postcond

-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

@[quickcheck]
theorem get!_eq_get
  {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (P : Prop):
  ∀ (i : Nat), i < arr.size → P ↔ ∀ (i : Fin arr.size), P := by
  sorry

@[quickcheck]
theorem get!_to_get!!
  {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]! = arr[i] := by
  simp [h]




-- set_option trace.quickcheck.safenorm true in
theorem replace_spec_satisfied (arr: Array Int) (k: Int) (h_precond : replace_precond (arr) (k)) :
    replace_postcond (arr) (k) (replace (arr) (k) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_84
