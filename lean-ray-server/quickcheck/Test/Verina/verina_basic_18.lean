import Quickcheck

set_option maxHeartbeats 0



@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  True

def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0

@[reducible, simp]
def sumOfDigits_postcond (n : Nat) (result: Nat) (h_precond : sumOfDigits_precond (n)) :=
  result - List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) = 0 ∧
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n))) - result = 0

def digitSumString (n : Nat) : Nat :=
  List.sum (List.map (fun c => Char.toNat c - Char.toNat '0') (String.toList (Nat.repr n)))

theorem sumOfDigits_spec_satisfied (n: Nat) (h_precond : sumOfDigits_precond (n)) :
    sumOfDigits_postcond (n) (sumOfDigits (n) h_precond) h_precond := by
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
