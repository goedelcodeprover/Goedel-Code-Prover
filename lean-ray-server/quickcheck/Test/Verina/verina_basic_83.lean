import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_83


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def concat_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : concat_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.size = a.size + b.size
    ∧ (∀ k, k < a.size → result[k]! = a[k]!)
    ∧ (∀ k, k < b.size → result[k + a.size]! = b[k]!)
  -- !benchmark @end postcond

-- !benchmark @end proof_aux

theorem concat_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : concat_precond (a) (b)) :
    concat_postcond (a) (b) (concat (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold concat_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_83
