import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_45


-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  -- !benchmark @start code
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def findProduct_postcond (lst : List Int) (result: Int) (h_precond : findProduct_precond (lst)) :=
  -- !benchmark @start postcond
  match firstEvenOddIndices lst with
  | some (ei, oi) => result = lst[ei]! * lst[oi]!
  | none => True
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem findProduct_spec_satisfied (lst: List Int) (h_precond : findProduct_precond (lst)) :
    findProduct_postcond (lst) (findProduct (lst) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold findProduct_postcond
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_45
