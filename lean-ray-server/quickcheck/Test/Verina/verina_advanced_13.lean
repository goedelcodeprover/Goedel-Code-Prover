import Quickcheck

set_option maxHeartbeats 200000
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_advanced_13


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def hasChordIntersection_precond (N : Nat) (chords : List (List Nat)) : Prop :=
  -- !benchmark @start precond
  N ≥ 2 ∧
  chords.all (fun chord => chord.length = 2 ∧ chord[0]! ≥ 1 ∧ chord[0]! ≤ 2 * N ∧ chord[1]! ≥ 1 ∧ chord[1]! ≤ 2 * N) ∧
  List.Nodup (chords.flatMap id)
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def hasChordIntersection (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) : Bool :=
  -- !benchmark @start code
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )

  let rec checkIntersection (stack : List (List Nat)) (remaining : List (List Nat)) : Bool :=
    match remaining with
    | [] => false
    | chord :: rest =>
      let a := chord[0]!
      let b := chord[1]!
      let newStack := stack.dropWhile (fun c => (c)[1]! < a)
      match newStack with
      | [] => checkIntersection (chord :: newStack) rest
      | top :: _ =>
        if top[1]! > a && top[1]! < b then
          true
        else
          checkIntersection (chord :: newStack) rest

  let rec insert (x : List Nat) (xs : List (List Nat)) : List (List Nat) :=
    match xs with
    | [] => [x]
    | y :: ys => if x[0]! < y[0]! then x :: xs else y :: insert x ys

  let rec sort (xs : List (List Nat)) : List (List Nat) :=
    match xs with
    | [] => []
    | x :: xs => insert x (sort xs)

  let sortedChords := sort sortedChords
  checkIntersection [] sortedChords
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def hasChordIntersection_postcond (N : Nat) (chords : List (List Nat)) (result: Bool) (h_precond : hasChordIntersection_precond (N) (chords)) : Prop :=
  -- !benchmark @start postcond
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )

  let rec hasIntersection (chord1 : List Nat) (chord2 : List Nat) : Bool :=
    let a1 := chord1[0]!
    let b1 := chord1[1]!
    let a2 := chord2[0]!
    let b2 := chord2[1]!
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)

  let rec checkAllPairs (chords : List (List Nat)) : Bool :=
    match chords with
    | [] => false
    | x :: xs =>
      if xs.any (fun y => hasIntersection x y) then true
      else checkAllPairs xs

  ((List.Pairwise (fun x y => !hasIntersection x y) sortedChords) → ¬ result) ∧
  ((sortedChords.any (fun x => chords.any (fun y => hasIntersection x y))) → result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasChordIntersection_spec_satisfied (N: Nat) (chords: List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    hasChordIntersection_postcond (N) (chords) (hasChordIntersection (N) (chords) h_precond) h_precond := by
  -- !benchmark @start proof
  -- Use 'normal' (100 tests) instead of 'extensive' (1000 tests) for faster testing
  quickcheck (config := { Quickcheck.Configuration.normal with enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_advanced_13
