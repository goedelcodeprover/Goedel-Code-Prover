-- import Quickcheck.Lemma.Attribute

-- namespace Quickcheck

-- /-!
--   Basic logical lemmas used by Quickcheck's normalization / simp layer.
-- -/

-- @[quickcheck]
-- theorem imp_to_or {p q : Prop} :
--     (p → q) ↔ (¬ p ∨ q) := by
--   constructor
--   sorry
--   sorry

-- @[quickcheck]
-- theorem split_imp_cases {p A B : Prop} [Decidable p] :
--     ((p → A) ∧ (¬ p → B)) ↔ ((p ∧ A) ∨ (¬ p ∧ B)) := by
--   constructor
--   · intro h
--     by_cases hp : p
--     · -- p holds: use the first implication
--       apply Or.inl
--       exact And.intro hp (h.1 hp)
--     · -- ¬ p holds: use the second implication
--       have hnp : ¬ p := hp
--       apply Or.inr
--       exact And.intro hnp (h.2 hnp)
--   · intro h
--     constructor
--     · -- p → A
--       intro hp
--       cases h with
--       | inl h₁ =>
--           -- we are in the p-branch
--           exact h₁.2
--       | inr h₂ =>
--           -- p contradicts ¬ p
--           cases h₂.1 hp
--     · -- ¬ p → B
--       intro hnp
--       cases h with
--       | inl h₁ =>
--           -- ¬ p contradicts p
--           cases hnp h₁.1
--       | inr h₂ =>
--           -- we are in the ¬ p-branch
--           exact h₂.2

-- @[quickcheck]
-- theorem ofNat_eq_coe : Int.ofNat n = Nat.cast n := rfl

-- end Quickcheck
