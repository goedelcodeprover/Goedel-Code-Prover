import Quickcheck

set_option maxHeartbeats 0



@[reducible]
def insertionSort_precond (xs : List Int) : Prop :=
  True

def insertionSort (xs : List Int) (h_precond : insertionSort_precond (xs)) : List Int :=
    let rec insert (x : Int) (ys : List Int) : List Int :=
      match ys with
      | []      => [x]
      | y :: ys' =>
        if x <= y then
          x :: y :: ys'
        else
          y :: insert x ys'

    let rec sort (arr : List Int) : List Int :=
      match arr with
      | []      => []
      | x :: xs => insert x (sort xs)

    sort xs

@[reducible]
def insertionSort_postcond (xs : List Int) (result: List Int) (h_precond : insertionSort_precond (xs)) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

theorem insertionSort_spec_satisfied (xs: List Int) (h_precond : insertionSort_precond (xs)) :
    insertionSort_postcond (xs) (insertionSort (xs) h_precond) h_precond := by
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })
