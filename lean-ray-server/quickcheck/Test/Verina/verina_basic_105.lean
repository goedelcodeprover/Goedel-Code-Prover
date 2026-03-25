import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_105


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def arrayProduct_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size
  -- !benchmark @end precond


-- !benchmark @start code_aux
def loop (a b : Array Int) (len : Nat) : Nat → Array Int → Array Int
  | i, c =>
    if i < len then
      let a_val := if i < a.size then a[i]! else 0
      let b_val := if i < b.size then b[i]! else 0
      let new_c := Array.set! c i (a_val * b_val)
      loop a b len (i+1) new_c
    else c
-- !benchmark @end code_aux


def arrayProduct (a : Array Int) (b : Array Int) (h_precond : arrayProduct_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let len := a.size
  let c := Array.mkArray len 0
  loop a b len 0 c
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def arrayProduct_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : arrayProduct_precond (a) (b)) :=
  -- !benchmark @start postcond
  (result.size = a.size) ∧ (∀ i, i < a.size → a[i]! * b[i]! = result[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem arrayProduct_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : arrayProduct_precond (a) (b)) :
    arrayProduct_postcond (a) (b) (arrayProduct (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_105
