-- import Quickcheck

def foo (a b : Nat) : Nat :=
  if h : b = 0 then
    a
  else
    foo b (a % b)
  termination_by b
  decreasing_by
    simp_wf
    exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

-- postcond
def IsGCD (d a b : Nat) : Prop :=
  d ∣ a ∧ d ∣ b ∧ ∀ c, c ∣ a → c ∣ b → c ∣ d

-- invariant
theorem dvd_mod_iff {a b c : Nat} (hb : b ≠ 0) :
  c ∣ a ∧ c ∣ b ↔ c ∣ b ∧ c ∣ (a % b) := by
  constructor
  · intro ⟨ha, hb_div⟩
    constructor
    · exact hb_div
    · have : a = b * (a / b) + a % b := by rw [Nat.div_add_mod a b]
      rw [this] at ha
      have h1 : c ∣ b * (a / b) := Nat.dvd_trans hb_div (Nat.dvd_mul_right b (a / b))
      have h2 : c ∣ (b * (a / b) + a % b) - b * (a / b) := Nat.dvd_sub ha h1
      simp at h2
      exact h2
  · intro ⟨hb_div, hmod⟩
    constructor
    · have : a = b * (a / b) + a % b := by
        rw [Nat.div_add_mod a b]
      rw [this]
      apply Nat.dvd_add
      · exact Nat.dvd_trans hb_div (Nat.dvd_mul_right b (a / b))
      · exact hmod
    · exact hb_div

-- proof
theorem foo_spec (a b : Nat) : IsGCD (foo a b) a b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
    by_cases hb : b = 0
    · -- Case: b = 0
      unfold foo
      simp [hb]
      constructor
      · exact Nat.dvd_refl a
      · constructor
        · exact Nat.dvd_zero a
        · intro c hca hcb
          exact hca
    · -- Case: b ≠ 0
      have hmod_lt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
      have ih_rec : IsGCD (foo b (a % b)) b (a % b) := ih (a % b) hmod_lt b
      unfold foo
      simp [hb]
      constructor
      · -- foo b (a % b) divides a
        have div_eq : b * (a / b) + a % b = a := Nat.div_add_mod a b
        have h1 : foo b (a % b) ∣ b * (a / b) := Nat.dvd_trans ih_rec.1 (Nat.dvd_mul_right b (a / b))
        have h2 : foo b (a % b) ∣ a % b := ih_rec.2.1
        have h3 : foo b (a % b) ∣ b * (a / b) + a % b := Nat.dvd_add h1 h2
        rwa [div_eq] at h3
      · -- foo b (a % b) divides b and is greatest
        constructor
        · exact ih_rec.1
        · -- foo b (a % b) is the greatest common divisor
          intro c hca hcb
          have := (dvd_mod_iff hb).mp ⟨hca, hcb⟩
          exact ih_rec.2.2 c this.1 this.2
