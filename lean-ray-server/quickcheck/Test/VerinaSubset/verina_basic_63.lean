import Quickcheck
import Quickcheck.Datatype.Float


set_option maxHeartbeats 0



namespace verina_basic_63

def absDiff (a b : Float) : Float :=
  if a - b < 0.0 then b - a else a - b

@[reducible, simp]
def has_close_elements_precond (numbers : List Float) (threshold : Float) : Prop :=
  threshold ≥ 0.0

def has_close_elements (numbers : List Float) (threshold : Float) (h_precond : has_close_elements_precond (numbers) (threshold)) : Bool :=
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

@[reducible, simp]
def has_close_elements_postcond (numbers : List Float) (threshold : Float) (result: Bool) (h_precond : has_close_elements_precond (numbers) (threshold)) :=
  ¬ result ↔ (List.Pairwise (fun a b => absDiff a b ≥ threshold) numbers)

theorem has_close_elements_spec_satisfied (numbers: List Float) (threshold: Float) (h_precond : has_close_elements_precond (numbers) (threshold)) :
    has_close_elements_postcond (numbers) (threshold) (has_close_elements (numbers) (threshold) h_precond) h_precond := by
    unfold has_close_elements_postcond
    unfold has_close_elements_precond at h_precond
    quickcheck (config := { Quickcheck.Configuration.extensive with decidableBound := some 100 })


end verina_basic_63
