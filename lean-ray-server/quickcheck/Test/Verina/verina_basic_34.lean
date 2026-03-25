import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_34


-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  -- !benchmark @start code
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : findEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  (∀ x, x ∈ result → isEven x ∧ x ∈ arr.toList) ∧
  (∀ x, x ∈ arr.toList → isEven x → x ∈ result) ∧
  (∀ x y, x ∈ arr.toList → y ∈ arr.toList →
    isEven x → isEven y →
    arr.toList.idxOf x ≤ arr.toList.idxOf y →
    result.toList.idxOf x ≤ result.toList.idxOf y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    findEvenNumbers_postcond (arr) (findEvenNumbers (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_34
