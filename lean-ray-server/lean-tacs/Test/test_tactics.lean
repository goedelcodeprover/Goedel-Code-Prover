import Tacs.Tactic
import Tacs.InductionGrind

-- Precondition auxiliary definitions
def Nat.isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else
    let rec check (i : Nat) : Bool :=
      if i * i > n then true
      else if n % i == 0 then false
      else check (i + 1)
    termination_by n - i
    decreasing_by apply PASS_PROOF
    check 2

example (xs : List Int) (i : Int) (h : 0 ≤ i) :
  i.toNat < xs.length → (xs.get? i.toNat).isSome := by
  simp_grind_induct
