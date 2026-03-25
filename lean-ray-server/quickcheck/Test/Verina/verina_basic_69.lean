import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_69


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ a[i]! = e
  -- !benchmark @end precond


-- !benchmark @start code_aux
def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0
-- !benchmark @end code_aux


def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  -- !benchmark @start code
  linearSearchAux a e 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  (result < a.size) ∧ (a[result]! = e) ∧ (∀ k : Nat, k < result → a[k]! ≠ e)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_69
