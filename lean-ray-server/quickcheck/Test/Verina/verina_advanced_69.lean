import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_69


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) xs
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  -- !benchmark @start code
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def searchInsert_postcond (xs : List Int) (target : Int) (result: Nat) (h_precond : searchInsert_precond (xs) (target)) : Prop :=
  -- !benchmark @start postcond
  let allBeforeLess := (List.range result).all (fun i => xs[i]! < target)
  let inBounds := result ≤ xs.length
  let insertedCorrectly :=
    result < xs.length → target ≤ xs[result]!
  inBounds ∧ allBeforeLess ∧ insertedCorrectly
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem searchInsert_spec_satisfied (xs: List Int) (target: Int) (h_precond : searchInsert_precond (xs) (target)) :
    searchInsert_postcond (xs) (target) (searchInsert (xs) (target) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_69
