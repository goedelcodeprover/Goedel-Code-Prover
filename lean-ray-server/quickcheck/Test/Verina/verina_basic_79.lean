import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_79


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ x < a.size
  -- !benchmark @end precond


-- !benchmark @start code_aux
def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1
-- !benchmark @end code_aux


def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  -- !benchmark @start code
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def onlineMax_postcond (a : Array Int) (x : Nat) (result: Int × Nat) (h_precond : onlineMax_precond (a) (x)) :=
  -- !benchmark @start postcond
  let (m, p) := result;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, i < x → a[i]! ≤ m) ∧
  (∃ i, i < x ∧ a[i]! = m) ∧
  ((p < a.size - 1) → (∀ i, i < p → a[i]! < a[p]!)) ∧
  ((∀ i, x ≤ i → i < a.size → a[i]! ≤ m) → p = a.size - 1)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

set_option trace.quickcheck.adaptive true in
theorem onlineMax_spec_satisfied (a: Array Int) (x: Nat) (h_precond : onlineMax_precond (a) (x)) :
    onlineMax_postcond (a) (x) (onlineMax (a) (x) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold onlineMax_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })


  -- !benchmark @end proof
end verina_basic_79
