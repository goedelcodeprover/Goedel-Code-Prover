/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zenali
-/

import Lean
import Quickcheck.Lemma.Attribute

/-!
# Lemmas: Converting Existential Quantifiers to Array.any

This module provides lemmas for converting existential quantifiers over arrays
to decidable `Array.any` forms. These lemmas are tagged with `@[quickcheck]` and
used by SafeNorm for normalization.
-/

namespace Quickcheck.Lemma

/--
Convert `match xs with | [] => P | _ => Q` to `if xs.isEmpty then P else Q`.

This lemma makes match expressions decidable by converting them to if-then-else.
Match expressions often fail to synthesize Decidable instances, while if-then-else
automatically inherits decidability from its branches.
-/
@[quickcheck]
theorem list_match_empty_to_ite {α : Type _} (xs : List α) (P Q : Prop) [Decidable P] [Decidable Q] :
    (match xs with | [] => P | _ => Q) ↔ (if xs.isEmpty then P else Q) := by
  cases xs <;> simp

/--
Convert unbounded `∃ k : Int, x = n * k` to decidable `x % n = 0` (for non-zero n).

This is a general lemma for converting existential quantifiers over infinite Int
to decidable modulo checks. For quickcheck purposes, this is safe because:
- If x is divisible by n (x % n = 0), then k = x / n witnesses the existential
- If x is not divisible by n, no such k exists

This works for any concrete integer n ≠ 0 that appears in the goal.
-/
@[quickcheck]
theorem exists_int_multiple_to_mod (x n : Int) :
    (∃ k : Int, x = n * k) ↔ (x % n = 0) := by
  constructor
  · intro ⟨k, hk⟩
    -- If x = n * k, then x % n = 0
    rw [hk]
    simp [Int.mul_emod_right]
  · intro h
    -- If x % n = 0, then ∃ k, x = n * k
    -- Witness: k = x / n
    exists x / n
    -- Use Int.ediv_add_emod: x = n * (x / n) + x % n
    have : x = n * (x / n) + x % n := by rw [Int.mul_ediv_add_emod]
    simp [h] at this
    exact this

/--
Convert `∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!` to `a.any fun x => b.any fun y => x = y`.

This is the key lemma for converting nested existential quantifiers over arrays
to decidable Array.any form.
-/
@[quickcheck]
theorem exists_array_index_pair_eq_to_any {α : Type _} [Inhabited α] [DecidableEq α] (a b : Array α) :
    (∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!) ↔
    (a.any fun x => b.any fun y => decide (x = y)) := by
  constructor
  · intro h
    obtain ⟨i, j, hi, hj, heq⟩ := h
    -- If ∃ i j, i < a.size ∧ j < b.size ∧ a[i]! = b[j]!, then a.any ... b.any ... returns true
    rw [Array.any_eq_true]
    exists i, hi
    -- Show that (fun x => b.any fun y => decide (x = y)) a[i] = true
    rw [Array.any_eq_true]
    exists j, hj
    -- Show that decide (a[i] = b[j]) = true
    -- Note: a[i]! = a[i] when we have hi : i < a.size
    rw [decide_eq_true]
    simp_all only [getElem!_pos]
  · intro h
    -- If a.any fun x => b.any fun y => decide (x = y) is true, then there exists indices
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, hb⟩ := h
    rw [Array.any_eq_true] at hb
    obtain ⟨j, hj, heq⟩ := hb
    -- heq is: decide (a[i] = b[j]) = true, so a[i] = b[j]
    have : a[i] = b[j] := by
      rw [decide_eq_true_iff] at heq
      exact heq
    -- Convert a[i] = b[j] to a[i]! = b[j]!
    have : a[i]! = b[j]! := by
      simp_all only [getElem!_pos]
    exact ⟨i, j, hi, hj, this⟩

/--
Convert `∃ i, i < a.size ∧ P (a[i]!)` to `a.any fun x => P x`.

General lemma for single existential quantifier with any predicate P.
-/
@[quickcheck]
theorem exists_array_index_to_any {α : Type _} [Inhabited α] (a : Array α) (P : α → Prop) [DecidablePred P] :
    (∃ i, i < a.size ∧ P (a[i]!)) ↔
    (a.any fun x => decide (P x)) := by
  constructor
  · intro h
    obtain ⟨i, hi, hP⟩ := h
    -- If ∃ i, i < a.size ∧ P (a[i]!), then a.any returns true
    -- Array.any_eq_true says: as.any p = true ↔ ∃ i x, p as[i] = true
    -- where x is a proof that i < as.size
    rw [Array.any_eq_true]
    -- We need to show ∃ i x, (fun x => decide (P x)) a[i] = true
    -- where x is a proof that i < a.size
    exists i, hi
    -- Show that decide (P a[i]) = true
    rw [decide_eq_true]
    -- a[i] in Array.any_eq_true is a.get i hi (same as a[i]!)
    -- Both are definitionally equal when we have the proof
    -- Use congr to show P a[i] = P (a[i]!)
    congr 1
    -- a[i] = a[i]! when both have the same proof hi
    simp_all only [getElem!_pos]
  · intro h
    -- If a.any fun x => decide (P x) is true, then there exists an index
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, hDec⟩ := h
    -- hDec is: (fun x => decide (P x)) a[i] = true, i.e., decide (P a[i]) = true
    -- So P a[i] is true
    have hP : P a[i] := by
      rw [decide_eq_true_iff] at hDec
      exact hDec
    -- hi is already the proof that i < a.size
    -- We need to show P (a[i]!) but we have P a[i]
    exists i, hi
    -- P a[i] = P (a[i]!) when both use the same proof hi
    simp_all only [getElem!_pos]

/--
Convert `∃ i, i < a.size ∧ a[i]! = x` to `a.any fun y => y = x`.

This lemma handles the common case of checking if an array contains a specific value.
It's more specific than `exists_array_index_to_any` but matches the pattern `a[i]! = x` directly.
-/
@[quickcheck]
theorem exists_array_index_eq {α : Type _} [Inhabited α] [DecidableEq α] (a : Array α) (x : α) :
    (∃ i, i < a.size ∧ a[i]! = x) ↔ (a.any fun y => decide (y = x)) := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := h
    rw [Array.any_eq_true]
    exists i, hi
    rw [decide_eq_true]
    simp_all only [getElem!_pos]
  · intro h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, heq⟩ := h
    exists i, hi
    rw [decide_eq_true_iff] at heq
    simp_all only [getElem!_pos]

/--
Convert `∃ i, i < a.size ∧ a[i]! < x` to `a.any fun y => decide (y < x)`.

This lemma handles the common case of checking if an array contains a value less than a given value.
It's more specific than `exists_array_index_to_any` but matches the pattern `a[i]! < x` directly.
-/
@[quickcheck]
theorem exists_array_index_lt {α : Type _} [Inhabited α] [LT α] [∀ a b : α, Decidable (a < b)] (a : Array α) (x : α) :
    (∃ i, i < a.size ∧ a[i]! < x) ↔ (a.any fun y => decide (y < x)) := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := h
    rw [Array.any_eq_true]
    exists i, hi
    rw [decide_eq_true]
    simp_all only [getElem!_pos]
  · intro h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, heq⟩ := h
    exists i, hi
    rw [decide_eq_true_iff] at heq
    simp_all only [getElem!_pos]

/--
Convert `∃ i, i < a.size ∧ a[i]! < x ∧ ∀ j, j < a.size → a[j]! ≠ a[i]! → a[j]! ≥ x`
to `a.any fun v => v < x ∧ a.all fun w => w < x → w = v`.

This lemma handles the common case of checking if an array contains a value less than a given value,
and all other values are at least the given value.
It's more specific than `exists_array_index_to_any` but matches the pattern `a[i]! < x ∧ ∀ j, j < a.size → a[j]! ≠ a[i]! → a[j]! ≥ x` directly.
-/
@[quickcheck]
theorem exists_array_index_min (a : Array Int) (x : Int) :
  (∃ i, i < a.size ∧ a[i]! < x ∧ ∀ j, j < a.size → a[j]! ≠ a[i]! → a[j]! ≥ x) ↔
    (a.any (fun v => v < x ∧ a.all (fun w => w < x → w = v))) := by
  constructor
  · -- Forward direction: ∃ i ... → a.any ...
    intro ⟨i, hi, hlt, hall⟩
    rw [Array.any_eq_true]
    exists i, hi
    simp
    constructor
    · -- Show decide (a[i] < x) = true
      simp_all only [getElem!_pos]
    · -- Show a.all (fun w => decide (w < x → w = a[i])) = true
      intro k hk
      by_cases h_eq : a[k]! = a[i]!
      · simp_all only [getElem!_pos]
        simp only [or_true]
      · simp_all [getElem!_pos]
  · -- Backward direction: a.any ... → ∃ i ...
    intro h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, h_prop⟩ := h
    simp at h_prop
    exists i, hi
    constructor
    · -- Show a[i]! < x
      have : a[i] = a[i]! := (getElem!_pos a i hi).symm
      rw [← this]
      exact h_prop.1
    · -- Show ∀ j, j < a.size → a[j]! ≠ a[i]! → a[j]! ≥ x
      intro j hj h_ne
      simp only [ge_iff_le]
      simp_all [getElem!_pos]
      have := h_prop.2 j
      simp [hj] at this
      simp [h_ne] at this
      simp [this]

-- /--
-- Convert `∃ i, i < a.size ∧ R (a[i]!) x` to `a.any fun y => decide (R y x)`.

-- This is a general lemma for binary relations. It handles patterns like:
-- - `∃ i, i < a.size ∧ a[i]! < x`
-- - `∃ i, i < a.size ∧ a[i]! ≤ x`
-- - `∃ i, i < a.size ∧ a[i]! > x`
-- where R is any decidable binary relation.
-- -/
-- @[quickcheck]
-- theorem exists_array_index_rel {α β : Type _} [Inhabited α] (a : Array α) (x : β)
--     (R : α → β → Prop) [∀ a b, Decidable (R a b)] :
--     (∃ i, i < a.size ∧ R (a[i]!) x) ↔ (a.any fun y => decide (R y x)) := by
--   constructor
--   · intro h
--     obtain ⟨i, hi, hR⟩ := h
--     rw [Array.any_eq_true]
--     exists i, hi
--     rw [decide_eq_true]
--     grind
--   · intro h
--     rw [Array.any_eq_true] at h
--     obtain ⟨i, hi, hR⟩ := h
--     exists i, hi
--     rw [decide_eq_true_iff] at hR
--     grind

-- /--
-- Convert `∃ i, i < a.size ∧ a[i]! < x` to `a.any fun y => decide (y < x)`.

-- Specialized version for less-than relation on types with LT and decidability.
-- -/
-- @[quickcheck]
-- theorem exists_array_index_lt {α : Type _} [Inhabited α] [LT α] [∀ a b : α, Decidable (a < b)]
--     (a : Array α) (x : α) :
--     (∃ i, i < a.size ∧ a[i]! < x) ↔ (a.any fun y => decide (y < x)) := by
--   exact exists_array_index_rel a x (· < ·)

-- /--
-- Convert `∃ i, i < a.size ∧ a[i]! > x` to `a.any fun y => decide (y > x)`.

-- Specialized version for greater-than relation.
-- -/
-- @[quickcheck]
-- theorem exists_array_index_gt {α : Type _} [Inhabited α] [LT α] [∀ a b : α, Decidable (a < b)]
--     (a : Array α) (x : α) :
--     (∃ i, i < a.size ∧ a[i]! > x) ↔ (a.any fun y => decide (y > x)) := by
--   exact exists_array_index_rel a x (· > ·)

-- /--
-- Convert `∃ i, i < a.size ∧ x = a[i]!` to `a.any fun y => decide (x = y)`.

-- This handles the reversed equality pattern.
-- -/
-- @[quickcheck]
-- theorem exists_array_index_eq_rev (a : Array α) (x : α) :
--     (∃ i, i < a.size ∧ x = a[i]!) ↔ (a.any fun y => decide (x = y)) := by
--   constructor
--   · intro h
--     obtain ⟨i, hi, heq⟩ := h
--     rw [Array.any_eq_true]
--     exists i, hi
--     rw [decide_eq_true]
--     grind
--   · intro h
--     rw [Array.any_eq_true] at h
--     obtain ⟨i, hi, heq⟩ := h
--     exists i, hi
--     rw [decide_eq_true_iff] at heq
--     grind

-- /--
-- Convert `∃ j, j < a.size ∧ a[j]! < x ∧ (∀ k, k < a.size → a[k]! ≠ a[j]! → a[k]! ≥ x)`
-- to `a.any (fun y => y < x ∧ a.all (fun z => z = y ∨ z ≥ x)) = true`.

-- This handles the "unique minimum less than x" pattern:
-- "there exists a unique value less than x, and all other values are at least x".

-- This is commonly used in "second smallest" specifications where we need to express:
-- - There is a minimum value less than the target
-- - All other distinct values are at least the target

-- Note: Due to the complexity of mixing a[j]! with Array.any/all semantics,
-- this lemma uses sorry. In practice, SafeNorm will apply simpler component lemmas.
-- -/
-- @[quickcheck]
-- theorem exists_unique_min_to_any {α : Type _} [Inhabited α] [LT α] [LE α]
--     [DecidableEq α] [∀ a b : α, Decidable (a < b)] [∀ a b : α, Decidable (a ≥ b)]
--     (a : Array α) (x : α) :
--     (∃ j, j < a.size ∧ a[j]! < x ∧
--       ∀ k, k < a.size → a[k]! ≠ a[j]! → a[k]! ≥ x) ↔
--     ((a.any fun y => decide (y < x && (a.all fun z => decide (z = y ∨ z ≥ x)))) = true) := by
--   constructor
--   · -- Forward direction: ∃ j ... → a.any ...
--     intro ⟨j, hj, hlt, hall⟩
--     rw [Array.any_eq_true]
--     exists j, hj
--     simp
--     constructor
--     · -- Show a[j] < x
--       have : a[j] = a[j]! := (getElem!_pos a j hj).symm
--       rw [this]
--       exact hlt
--     · -- Show ∀ (i : Nat) (x_1 : i < a.size), a[i] = a[j] ∨ x ≤ a[i]
--       intro k hk
--       by_cases h_eq : a[k] = a[j]
--       · left
--         exact h_eq
--       · right
--         have h_ne : a[k]! ≠ a[j]! := by
--           intro h_contra
--           have : a[k] = a[j] := by
--             have hk' : a[k] = a[k]! := (getElem!_pos a k hk).symm
--             have hj' : a[j] = a[j]! := (getElem!_pos a j hj).symm
--             rw [hk', h_contra, ← hj']
--           exact h_eq this
--         have h_ge : a[k]! ≥ x := hall k hk h_ne
--         have h_le : x ≤ a[k]! := h_ge
--         have h_eq : a[k] = a[k]! := (getElem!_pos a k hk).symm
--         rw [← h_eq] at h_le
--         exact h_le
--   · -- Backward direction: a.any ... → ∃ j ...
--     intro h
--     rw [Array.any_eq_true] at h
--     obtain ⟨j, hj, h_prop⟩ := h
--     simp at h_prop
--     exists j, hj
--     constructor
--     · -- Show a[j]! < x
--       have h_lt : a[j] < x := h_prop.1
--       have h_eq : a[j] = a[j]! := (getElem!_pos a j hj).symm
--       rw [← h_eq]
--       exact h_lt
--     · -- Show ∀ k, k < a.size → a[k]! ≠ a[j]! → a[k]! ≥ x
--       intro k hk h_ne
--       have h_all := h_prop.2
--       have : a[k] = a[j] ∨ x ≤ a[k] := h_all k hk
--       cases this with
--       | inl h_eq =>
--         -- If a[k] = a[j], contradiction with h_ne
--         exfalso
--         apply h_ne
--         have hk' : a[k]! = a[k] := getElem!_pos a k hk
--         have hj' : a[j]! = a[j] := getElem!_pos a j hj
--         rw [hk', hj', h_eq]
--       | inr h_le =>
--         -- x ≤ a[k], so a[k]! ≥ x
--         have h_eq : a[k] = a[k]! := (getElem!_pos a k hk).symm
--         have : a[k]! ≥ x := by
--           rw [← h_eq]
--           exact h_le
--         exact this

-- /--
-- Simplify `Array.all` with conditional `decide` expressions.

-- Converts `a.all (fun x => if P x then decide (Q x) else decide (R x)) = true`
-- to `a.all (fun x => if P x then Q x else R x)`.

-- This is useful for normalizing expressions where we check if all elements satisfy
-- a conditional property, removing the redundant `decide` and `= true` wrapper.
-- -/
-- @[quickcheck]
-- theorem array_all_conditional_decide {α : Type _} [Inhabited α] (a : Array α)
--     (P : α → Prop) (Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R] :
--     (a.all fun x => if P x then decide (Q x) else decide (R x)) = true ↔
--     (a.all fun x => if P x then Q x else R x) := by
--   constructor
--   · intro h
--     rw [Array.all_eq_true] at h
--     rw [Array.all_eq_true]
--     intro i hi
--     have h1 := h i hi
--     by_cases hP : P a[i]
--     · -- Case: P a[i] is true
--       simp [hP] at h1
--       simp [hP, h1]
--     · -- Case: P a[i] is false
--       simp [hP] at h1
--       simp [hP, h1]
--   · intro h
--     rw [Array.all_eq_true] at h
--     rw [Array.all_eq_true]
--     intro i hi
--     have h1 := h i hi
--     by_cases hP : P a[i]
--     · -- Case: P a[i] is true
--       have hQ : Q a[i] := by
--         simp [hP] at h1
--         exact h1
--       simp [hP, hQ]
--     · -- Case: P a[i] is false
--       have hR : R a[i] := by
--         simp [hP] at h1
--         exact h1
--       simp [hP, hR]

/--

Convert `∀ j, j < (arr[i]!).size → P j` to `∀ j : Fin (arr[i]!).size, P j`.

This lemma handles the common case of iterating over the elements of an array.
It's more specific than `forall_array_index_to_any` but matches the pattern `j < (arr[i]!).size` directly.

**Priority note**: More specific lemmas should be assigned higher priority, while more general lemmas should be assigned lower priority. This ensures that specific patterns are matched first before falling back to general transformations.
-/
@[quickcheck]
theorem forall_array_index_to_fin (arr : Array (Array α)) (i : Nat) (P : Nat → Prop):
   (∀ (j : Nat), j < (arr[i]!).size → P j) ↔ ∀ (j : Fin (arr[i]!).size), P j.val := by
  constructor
  · intro h j
    exact h j.val j.isLt
  · intro h j hj
    have : j < (arr[i]!).size := hj
    let j' : Fin (arr[i]!).size := ⟨j, this⟩
    exact h j'

@[quickcheck low]
theorem get!_to_get
  {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (h : i < arr.size) :
  arr[i]! = arr[i] := by
  simp [h]

end Quickcheck.Lemma
