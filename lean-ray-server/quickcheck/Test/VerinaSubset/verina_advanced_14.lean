import Quickcheck


set_option maxHeartbeats 0

namespace verina_advanced_14

@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n

@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)

theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })

end verina_advanced_14
