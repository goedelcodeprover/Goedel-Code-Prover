import Quickcheck

set_option maxHeartbeats 0

set_option linter.unusedVariables false

def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0

@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)

def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]?.getD 0
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]?.getD 0 - a[o]?.getD 0
      | _, _ => findFirstEvenOdd (i + 1) firstEven firstOdd
    else
      0
  findFirstEvenOdd 0 none none

@[reducible, simp]
def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]?.getD 0) ∧ isOdd (a[j]?.getD 0) ∧
    result = a[i]?.getD 0 - a[j]?.getD 0 ∧
    (∀ k, k < i → isOdd (a[k]?.getD 0)) ∧ (∀ k, k < j → isEven (a[k]?.getD 0))

theorem firstEvenOddDifference_spec_satisfied (a: Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    firstEvenOddDifference_postcond (a) (firstEvenOddDifference (a) h_precond) h_precond := by
    quickcheck (config := { Quickcheck.Configuration.extensive with quiet := true, randomSeed := some 42 })
