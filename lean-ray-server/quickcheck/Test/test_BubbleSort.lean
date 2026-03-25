/-
  Bubble Sort in Lean4
  ====================
  Sorting List Nat using bubble sort
-/

import Std

open Nat

/-- One bubble pass: scan once, pushing larger elements to the right. -/
def bubbleStep : List Nat → List Nat
| []        => []
| [x]       => [x]
| x :: y :: xs =>
  if x ≤ y then
    x :: bubbleStep (y :: xs)
  else
    y :: bubbleStep (x :: xs)

/-- Auxiliary: run n bubble passes. -/
@[reducible, simp]
def bubblesortAux : Nat → List Nat → List Nat
| 0,     xs => xs
| n + 1, xs => bubblesortAux n (bubbleStep xs)

/-- Main bubble sort function. -/
@[reducible, simp]
def bubblesort (xs : List Nat) : List Nat :=
  bubblesortAux xs.length xs

@[reducible, simp]
def postcond (xs : List Nat) (result: List Nat) : Prop :=
  List.Pairwise (· ≤ ·) result ∧ List.isPerm xs result

theorem bubblesort_spec_satisfied (xs : List Nat) :
    postcond (xs) (bubblesort (xs)) := by
  apply And.intro
  · sorry
  · induction xs
    simp
    simp [List.isPerm]
    simp_all
    unfold bubbleStep
    split
    rename_i head tail tail_ih x_list heq
    simp at heq
    rename_i head' head tail tail_ih x_list heq
    by_cases heq_cases : head = []
    have : head.length = 0 := by simp [heq_cases]
    simp [this, heq]
    simp [List.isPerm]
    have : head.length = 1 := by simp_all
    simp [this, heq]
    unfold bubbleStep
    simp [List.isPerm]
    rename_i head tail tail_ih x_list x y xs heq
    by_cases hxy : x ≤ y
    simp [hxy]
