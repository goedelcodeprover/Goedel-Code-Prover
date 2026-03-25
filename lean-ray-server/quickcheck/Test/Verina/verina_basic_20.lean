import Quickcheck
-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

namespace verina_basic_20


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def uniqueProduct_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def uniqueProduct (arr : Array Int) (h_precond : uniqueProduct_precond (arr)) : Int :=
  -- !benchmark @start code
  let rec loop (i : Nat) (seen : Std.HashSet Int) (product : Int) : Int :=
    if i < arr.size then
      let x := arr[i]!
      if seen.contains x then
        loop (i + 1) seen product
      else
        loop (i + 1) (seen.insert x) (product * x)
    else
      product
  loop 0 Std.HashSet.empty 1
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def uniqueProduct_postcond (arr : Array Int) (result: Int) (h_precond : uniqueProduct_precond (arr)) :=
  -- !benchmark @start postcond
  result - (arr.toList.eraseDups.foldl (· * ·) 1) = 0 ∧
  (arr.toList.eraseDups.foldl (· * ·) 1) - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem uniqueProduct_spec_satisfied (arr: Array Int) (h_precond : uniqueProduct_precond (arr)) :
    uniqueProduct_postcond (arr) (uniqueProduct (arr) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_20
