import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_86


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  -- !benchmark @start precond
  offset ≥ 0
  -- !benchmark @end precond


-- !benchmark @start code_aux
def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b
-- !benchmark @end code_aux


def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  -- !benchmark @start code
  let len := a.size
  let default_val : Int := if len > 0 then a[0]! else 0
  let b0 := Array.mkArray len default_val
  rotateAux a offset 0 len b0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def rotate_postcond (a : Array Int) (offset : Int) (result: Array Int) (h_precond : rotate_precond (a) (offset)) :=
  -- !benchmark @start postcond
  result.size = a.size ∧
  (∀ i : Nat, i < a.size →
    result[i]! = a[Int.toNat ((Int.ofNat i + offset) % (Int.ofNat a.size))]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem rotate_spec_satisfied (a: Array Int) (offset: Int) (h_precond : rotate_precond (a) (offset)) :
    rotate_postcond (a) (offset) (rotate (a) (offset) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_86
