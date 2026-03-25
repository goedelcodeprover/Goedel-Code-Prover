import Quickcheck

namespace verina_basic_81


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)
-- !benchmark @end code_aux


def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  -- !benchmark @start code
  if y = 0 then (Int.ofNat x, 0) else divMod x y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def DivisionFunction_postcond (x : Nat) (y : Nat) (result: Int × Int) (h_precond : DivisionFunction_precond (x) (y)) :=
  -- !benchmark @start postcond
  let (r, q) := result;
  (y = 0 → r = Int.ofNat x ∧ q = 0) ∧
  (y ≠ 0 → (q * Int.ofNat y + r = Int.ofNat x) ∧ (0 ≤ r ∧ r < Int.ofNat y) ∧ (0 ≤ q))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.safenorm true
theorem DivisionFunction_spec_satisfied (x: Nat) (y: Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    DivisionFunction_postcond (x) (y) (DivisionFunction (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold DivisionFunction_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_81
