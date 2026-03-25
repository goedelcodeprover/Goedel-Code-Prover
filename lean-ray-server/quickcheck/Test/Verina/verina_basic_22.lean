import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

namespace verina_basic_22


-- !benchmark @start solution_aux
def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
  -- !benchmark @start code
  let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.empty
  let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
  res.toArray.insertionSort
  -- !benchmark @end code

-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def dissimilarElements_postcond (a : Array Int) (b : Array Int) (result: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :=
  -- !benchmark @start postcond
  result.all (fun x => inArray a x ≠ inArray b x)∧
  result.toList.Pairwise (· ≤ ·) ∧
  a.all (fun x => if x ∈ b then x ∉ result else x ∈ result) ∧
  b.all (fun x => if x ∈ a then x ∉ result else x ∈ result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


-- set_option trace.quickcheck.split true
-- set_option trace.quickcheck.safenorm true
theorem dissimilarElements_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    dissimilarElements_postcond (a) (b) (dissimilarElements (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold dissimilarElements_postcond
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, enableSafeNorm := false, quiet := true })

  -- !benchmark @end proof
end verina_basic_22
