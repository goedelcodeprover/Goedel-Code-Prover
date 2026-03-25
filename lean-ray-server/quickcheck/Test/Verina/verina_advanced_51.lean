import Quickcheck

set_option maxHeartbeats 0

@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b

def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged

def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  let merged := mergeSortedAux a b
  merged

@[reducible, simp]
def mergeSorted_postcond (a : List Int) (b : List Int) (result: List Int) (h_precond : mergeSorted_precond (a) (b)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧
  List.isPerm result (a ++ b)

theorem mergeSorted_spec_satisfied
    (a: List Int) (b: List Int) (h_precond : mergeSorted_precond (a) (b)) :
    mergeSorted_postcond (a) (b) (mergeSorted (a) (b) h_precond) h_precond := by
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
