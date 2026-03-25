import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_41


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  -- !benchmark @start code
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOnlyOneDistinctElement_postcond (a : Array Int) (result: Bool) (h_precond : hasOnlyOneDistinctElement_precond (a)) :=
  -- !benchmark @start postcond
  let l := a.toList
  (result → List.Pairwise (· = ·) l) ∧
  (¬ result → (l.any (fun x => x ≠ l[0]!)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOnlyOneDistinctElement_spec_satisfied (a: Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    hasOnlyOneDistinctElement_postcond (a) (hasOnlyOneDistinctElement (a) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_41
