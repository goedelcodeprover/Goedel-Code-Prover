import Quickcheck


set_option maxHeartbeats 0



namespace verina_basic_24

def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0

@[reducible, simp]
def aaa (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

def bbbb (a : Array Int) (h_precond : aaa (a)) : Int :=
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => findFirstEvenOdd (i + 1) firstEven firstOdd
    else
      0
  findFirstEvenOdd 0 none none

@[reducible, simp]
def ccc (a : Array Int) (result: Int) (h_precond : aaa (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))

/--
error: [Quickcheck Safety Error]
Partial function `GetElem?.getElem!` can panic.
Safe alternative: getElem? or get?

To fix: wrap partial functions with guards like `if l.length > 0 then ... else True`
Or disable SafeGuard: quickcheck (config := { enableSafeGuard := false })
-/
#guard_msgs in
theorem firstEvenOddDifference_spec_satisfied (a: Array Int) (h_precond : aaa (a)) :
    ccc (a) (bbbb (a) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.normal with enableSafeGuard := true, enableSafeNorm := true, quiet := true, randomSeed := some 42 })

end verina_basic_24
