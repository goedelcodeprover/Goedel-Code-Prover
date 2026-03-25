import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_52


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def BubbleSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a
-- !benchmark @end code_aux


def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  -- !benchmark @start code
  if a.size = 0 then a else bubbleOuter (a.size - 1) a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def BubbleSort_postcond (a : Array Int) (result: Array Int) (h_precond : BubbleSort_precond (a)) :=
  -- !benchmark @start postcond
  List.Pairwise (· ≤ ·) result.toList ∧ List.isPerm result.toList a.toList
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem BubbleSort_spec_satisfied (a: Array Int) (h_precond : BubbleSort_precond (a)) :
    BubbleSort_postcond (a) (BubbleSort (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_52
