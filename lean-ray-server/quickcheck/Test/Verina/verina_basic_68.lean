import Quickcheck

namespace verina_basic_68


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  -- !benchmark @start code
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def LinearSearch_postcond (a : Array Int) (e : Int) (result: Nat) (h_precond : LinearSearch_precond (a) (e)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧ (result = a.size ∨ a[result]! = e) ∧ (∀ i, i < result → a[i]! ≠ e)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem LinearSearch_spec_satisfied (a: Array Int) (e: Int) (h_precond : LinearSearch_precond (a) (e)) :
    LinearSearch_postcond (a) (e) (LinearSearch (a) (e) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })



  -- !benchmark @end proof
end verina_basic_68
