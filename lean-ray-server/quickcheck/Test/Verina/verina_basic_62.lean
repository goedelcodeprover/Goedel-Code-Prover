import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_62


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  -- !benchmark @start code
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Find_postcond (a : Array Int) (key : Int) (result: Int) (h_precond : Find_precond (a) (key)) :=
  -- !benchmark @start postcond
  (result = -1 ∨ (result ≥ 0 ∧ result < Int.ofNat a.size))
  ∧ ((result ≠ -1) → (a[(Int.toNat result)]! = key ∧ ∀ (i : Nat), i < Int.toNat result → a[i]! ≠ key))
  ∧ ((result = -1) → ∀ (i : Nat), i < a.size → a[i]! ≠ key)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Find_spec_satisfied (a: Array Int) (key: Int) (h_precond : Find_precond (a) (key)) :
    Find_postcond (a) (key) (Find (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_62
