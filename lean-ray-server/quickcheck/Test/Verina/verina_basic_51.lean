import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_51


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux
def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo
-- !benchmark @end code_aux


def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  -- !benchmark @start code
  binarySearchLoop a key 0 a.size
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def BinarySearch_postcond (a : Array Int) (key : Int) (result: Nat) (h_precond : BinarySearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  result ≤ a.size ∧
  ((a.take result).all (fun x => x < key)) ∧
  ((a.drop result).all (fun x => x ≥ key))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem BinarySearch_spec_satisfied (a: Array Int) (key: Int) (h_precond : BinarySearch_precond (a) (key)) :
    BinarySearch_postcond (a) (key) (BinarySearch (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_51
