import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_60


-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def FindEvenNumbers_postcond (arr : Array Int) (result: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :=
  -- !benchmark @start postcond
  result.all (fun x => isEven x && x ∈ arr) ∧
  List.Pairwise (fun (x, i) (y, j) => if i < j then arr.idxOf x ≤ arr.idxOf y else true) (result.toList.zipIdx)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem FindEvenNumbers_spec_satisfied (arr: Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    FindEvenNumbers_postcond (arr) (FindEvenNumbers (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_60
