import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_63


-- !benchmark @start solution_aux
def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  -- !benchmark @start precond
  threshold ≥ 0.0
  -- !benchmark @end precond


-- !benchmark @start code_aux
-- !benchmark @end code_aux


def has_close_elements (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
  -- !benchmark @start code
  let len := numbers.length
  let rec outer (idx : Nat) : Bool :=
    if idx < len then
      let rec inner (idx2 : Nat) : Bool :=
        if idx2 < idx then
          let a := numbers.getD idx2 0.0
          let b := numbers.getD idx 0.0
          let d := absDiff a b
          if d < threshold then true else inner (idx2 + 1)
        else
          false
      if inner 0 then true else outer (idx + 1)
    else
      false
  outer 0
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) (h_precond : has_close_elements_precond (numbers) (threshold)) :=
  -- !benchmark @start postcond
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem has_close_elements_spec_satisfied (numbers: List Float) (threshold: Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    has_close_elements_postcond (numbers) (threshold) (has_close_elements (numbers) (threshold) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_63
