import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_24


-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 == 0

def isOdd (n : Int) : Bool :=
  n % 2 != 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def firstEvenOddDifference_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 1 ∧
  (∃ x ∈ a, isEven x) ∧
  (∃ x ∈ a, isOdd x)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def firstEvenOddDifference (a : Array Int) (h_precond : firstEvenOddDifference_precond (a)) : Int :=
  -- !benchmark @start code
  let rec findFirstEvenOdd (i : Nat) (firstEven firstOdd : Option Nat) : Int :=
    if i < a.size then
      let x := a[i]!
      let firstEven := if firstEven.isNone && isEven x then some i else firstEven
      let firstOdd := if firstOdd.isNone && isOdd x then some i else firstOdd
      match firstEven, firstOdd with
      | some e, some o => a[e]! - a[o]!
      | _, _ => findFirstEvenOdd (i + 1) firstEven firstOdd
    else
      -- This case is impossible due to h2, but we need a value
      0
  findFirstEvenOdd 0 none none
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def firstEvenOddDifference_postcond (a : Array Int) (result: Int) (h_precond : firstEvenOddDifference_precond (a)) :=
  -- !benchmark @start postcond
  ∃ i j, i < a.size ∧ j < a.size ∧ isEven (a[i]!) ∧ isOdd (a[j]!) ∧
    result = a[i]! - a[j]! ∧
    (∀ k, k < i → isOdd (a[k]!)) ∧ (∀ k, k < j → isEven (a[k]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem firstEvenOddDifference_spec_satisfied (a: Array Int) (h_precond : firstEvenOddDifference_precond (a)) :
    firstEvenOddDifference_postcond (a) (firstEvenOddDifference (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_24
