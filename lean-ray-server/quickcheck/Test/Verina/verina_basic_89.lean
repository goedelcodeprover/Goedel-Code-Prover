import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_89


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SetToSeq_precond (s : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SetToSeq (s : List Int) (h_precond : SetToSeq_precond (s)) : List Int :=
  -- !benchmark @start code
  s.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SetToSeq_postcond (s : List Int) (result: List Int) (h_precond : SetToSeq_precond (s)) :=
  -- !benchmark @start postcond
  -- Contains exactly the elements of the set
  result.all (fun a => a ∈ s) ∧ s.all (fun a => a ∈ result) ∧
  -- All elements are unique in the result
  result.all (fun a => result.count a = 1) ∧
  -- The order of elements in the result is preserved
  List.Pairwise (fun a b => (result.idxOf a < result.idxOf b) → (s.idxOf a < s.idxOf b)) result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux

-- set_option trace.quickcheck.split true
theorem SetToSeq_spec_satisfied (s: List Int) (h_precond : SetToSeq_precond (s)) :
    SetToSeq_postcond (s) (SetToSeq (s) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold SetToSeq_postcond
  quickcheck (config := { Quickcheck.Configuration.normal with onlyDecidable := true, enableSafeNorm := true, quiet := true })
  -- !benchmark @end proof
end verina_basic_89
