import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_72


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc
-- !benchmark @end code_aux


def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  -- !benchmark @start postcond
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem append_spec_satisfied (a: Array Int) (b: Int) (h_precond : append_precond (a) (b)) :
    append_postcond (a) (b) (append (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_72
