import Quickcheck

import Std.Data.HashMap
open Std

set_option maxHeartbeats 0
set_option synthInstance.maxSize 512
set_option linter.unusedVariables false

def listToNat : List Nat → Nat
| []       => 0
| d :: ds  => d + 10 * listToNat ds

@[reducible]
def addTwoNumbers_precond (l1 : List Nat) (l2 : List Nat) : Prop :=
  l1.length > 0 ∧ l2.length > 0
  ∧ (l1.all (fun x => decide (x < 10)) = true) ∧ (l2.all (fun x => decide (x < 10)) = true)
  ∧ (if l1.length > 0 then (l1.getLast! ≠ 0 ∨ l1 = [0]) else True)
  ∧ (if l2.length > 0 then (l2.getLast! ≠ 0 ∨ l2 = [0]) else True)

def addTwoNumbers (l1 : List Nat) (l2 : List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : List Nat :=
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

@[reducible]
def addTwoNumbers_postcond (l1 : List Nat) (l2 : List Nat) (result: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) : Prop :=
  listToNat result = listToNat l1 + listToNat l2
  ∧
  (result.all (fun x => decide (x < 10)) = true)
  ∧
  result.length > 0
  ∧
  (if result.length > 0 then (result.getLast! ≠ 0 ∨ (l1 = [0] ∧ l2 = [0] ∧ result = [0])) else True)


-- Test with SafeGuard disabled
theorem addTwoNumbers_spec_satisfied (l1: List Nat) (l2: List Nat) (h_precond : addTwoNumbers_precond (l1) (l2)) :
    addTwoNumbers_postcond (l1) (l2) (addTwoNumbers (l1) (l2) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })
