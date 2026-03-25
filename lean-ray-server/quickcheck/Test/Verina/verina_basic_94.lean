import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_94


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def iter_copy_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def iter_copy (s : Array Int) (h_precond : iter_copy_precond (s)) : Array Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < s.size then
      match s[i]? with
      | some val => loop (i + 1) (acc.push val)
      | none => acc  -- This case shouldn't happen when i < s.size
    else
      acc
  loop 0 Array.empty
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def iter_copy_postcond (s : Array Int) (result: Array Int) (h_precond : iter_copy_precond (s)) :=
  -- !benchmark @start postcond
  (s.size = result.size) ∧ (∀ i : Nat, i < s.size → s[i]! = result[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem iter_copy_spec_satisfied (s: Array Int) (h_precond : iter_copy_precond (s)) :
    iter_copy_postcond (s) (iter_copy (s) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_94
