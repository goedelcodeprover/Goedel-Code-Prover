import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_37


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstOccurrence_precond (arr : Array Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findFirstOccurrence (arr : Array Int) (target : Int) (h_precond : findFirstOccurrence_precond (arr) (target)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = target then i
      else if a > target then -1
      else loop (i + 1)
    else -1
  loop 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findFirstOccurrence_postcond (arr : Array Int) (target : Int) (result: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :=
  -- !benchmark @start postcond
  (result ≥ 0 →
    arr[result.toNat]! = target ∧
    (∀ i : Nat, i < result.toNat → arr[i]! ≠ target)) ∧
  (result = -1 →
    (∀ i : Nat, i < arr.size → arr[i]! ≠ target))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findFirstOccurrence_spec_satisfied (arr: Array Int) (target: Int) (h_precond : findFirstOccurrence_precond (arr) (target)) :
    findFirstOccurrence_postcond (arr) (target) (findFirstOccurrence (arr) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_37
