import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_70


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ P (a[i]!)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else
      0
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch3_postcond (a : Array Int) (P : Int -> Bool) (result: Nat) (h_precond : LinearSearch3_precond (a) (P)) :=
  -- !benchmark @start postcond
  result < a.size ∧ P (a[result]!) ∧ (∀ k, k < result → ¬ P (a[k]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LinearSearch3_spec_satisfied (a: Array Int) (P: Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    LinearSearch3_postcond (a) (P) (LinearSearch3 (a) (P) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_70
