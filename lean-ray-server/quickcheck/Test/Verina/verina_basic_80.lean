import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_80


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def only_once_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1
-- !benchmark @end code_aux


def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  -- !benchmark @start code
  only_once_loop a key 0 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def count_occurrences {T : Type} [DecidableEq T] (a : Array T) (key : T) : Nat :=
  a.foldl (fun cnt x => if x = key then cnt + 1 else cnt) 0
-- !benchmark @end postcond_aux


@[reducible, simp]
def only_once_postcond (a : Array Int) (key : Int) (result: Bool) (h_precond : only_once_precond (a) (key)) :=
  -- !benchmark @start postcond
  ((count_occurrences a key = 1) → result) ∧
  ((count_occurrences a key ≠ 1) → ¬ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem only_once_spec_satisfied (a: Array Int) (key: Int) (h_precond : only_once_precond (a) (key)) :
    only_once_postcond (a) (key) (only_once (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_80
