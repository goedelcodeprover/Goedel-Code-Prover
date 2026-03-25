import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_49


-- !benchmark @start solution_aux
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  -- !benchmark @start code
  -- Creates list of (index, value) pairs
  let indexed := a.toList.zipIdx

  -- Find the first pair where the value is odd
  let found := List.find? (fun (x, _) => isOdd x) indexed

  -- Extract the index from the found pair (if any)
  Option.map (fun (_, i) => i) found
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findFirstOdd_postcond (a : Array Int) (result: Option Nat) (h_precond : findFirstOdd_precond (a)) :=
  -- !benchmark @start postcond
  match result with
  | some idx => idx < a.size ∧ isOdd (a[idx]!) ∧
    (∀ j, j < idx → ¬ isOdd (a[j]!))
  | none => ∀ i, i < a.size → ¬ isOdd (a[i]!)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.split true
-- set_option trace.quickcheck.safenorm true
theorem findFirstOdd_spec_satisfied (a: Array Int) (h_precond : findFirstOdd_precond (a)) :
    findFirstOdd_postcond (a) (findFirstOdd (a) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findFirstOdd_postcond
  -- preprocess
  quickcheck (config := { Quickcheck.Configuration.adaptive with enableSafeNorm := true, quiet := true })
  -- quickcheck (config := { Quickcheck.Configuration.adaptive with enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_49
