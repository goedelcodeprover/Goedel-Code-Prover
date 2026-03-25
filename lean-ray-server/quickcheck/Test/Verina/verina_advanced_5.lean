import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_5


-- !benchmark @start solution_aux
def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  -- !benchmark @start precond
  l1.length > 0 ∧ l2.length > 0 ∧
  (∀ d ∈ l1, d < 10) ∧ (∀ d ∈ l2, d < 10) ∧
  (l1.getLast! ≠ 0 ∨ l1 = [0]) ∧
  (l2.getLast! ≠ 0 ∨ l2 = [0])
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
  -- !benchmark @start code
  let rec addAux (l1 l2 : List Nat) (carry : Nat) : List Nat :=
    match l1, l2 with
    | [], [] =>
      if carry = 0 then [] else [carry]
    | h1::t1, [] =>
      let sum := h1 + carry
      (sum % 10) :: addAux t1 [] (sum / 10)
    | [], h2::t2 =>
      let sum := h2 + carry
      (sum % 10) :: addAux [] t2 (sum / 10)
    | h1::t1, h2::t2 =>
      let sum := h1 + h2 + carry
      (sum % 10) :: addAux t1 t2 (sum / 10)
  addAux l1 l2 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  -- !benchmark @start postcond
  listToNat result = listToNat l1 + listToNat l2 ∧
  (∀ d ∈ result, d < 10) ∧
  -- No leading zeros unless the result is zero
  (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0]))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

set_option synthInstance.maxSize 256
set_option trace.quickcheck true in
theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold addTwoNumbers_postcond
  quickcheck (config := { Quickcheck.Configuration.normal with decidableBound := some 100, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_5
