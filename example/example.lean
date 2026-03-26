import Mathlib
set_option maxHeartbeats 0

namespace verina_advanced_2

@[reducible, simp]
def LongestCommonSubsequence_precond (a : Array Int) (b : Array Int) : Prop :=
  True

def intMax (x y : Int) : Int :=
  if x < y then y else x

private lemma intMax_eq_max (x y : Int) : intMax x y = max x y := by
  simp [intMax, max_def]; omega

def LongestCommonSubsequence (a : Array Int) (b : Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Int :=
  let m := a.size
  let n := b.size

  let dp := Id.run do
    let mut dp := Array.mkArray (m + 1) (Array.mkArray (n + 1) 0)
    for i in List.range (m + 1) do
      for j in List.range (n + 1) do
        if i = 0 ∨ j = 0 then
          ()
        else if a[i - 1]! = b[j - 1]! then
          let newVal := ((dp[i - 1]!)[j - 1]!) + 1
          dp := dp.set! i (dp[i]!.set! j newVal)
        else
          let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
          dp := dp.set! i (dp[i]!.set! j newVal)
    return dp
  (dp[m]!)[n]!

@[reducible, simp]
def LongestCommonSubsequence_postcond (a : Array Int) (b : Array Int) (result: Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) : Prop :=
  let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse
  let subseqA := allSubseq a
  let subseqB := allSubseq b
  let commonSubseqLens := subseqA.filter (fun l => subseqB.contains l) |>.map (·.length)
  commonSubseqLens.contains result ∧ commonSubseqLens.all (· ≤ result)

-- Recursive LCS
def lcsRec (xs ys : List Int) : Nat :=
  match xs, ys with
  | [], _ => 0
  | (_ :: _), [] => 0
  | (x :: xs'), (y :: ys') =>
    if x = y then lcsRec xs' ys' + 1
    else Nat.max (lcsRec xs' (y :: ys')) (lcsRec (x :: xs') ys')
termination_by xs.length + ys.length

-- Optimality: every common sublist has length ≤ lcsRec
lemma lcsRec_optimal (s xs ys : List Int)
    (hx : s.Sublist xs) (hy : s.Sublist ys) : s.length ≤ lcsRec xs ys := by
  induction xs generalizing s ys with
  | nil => simp [List.sublist_nil.mp hx, lcsRec]
  | cons x xs ihx =>
    induction ys generalizing s with
    | nil => simp [List.sublist_nil.mp hy, lcsRec]
    | cons y ys ihy =>
      simp only [lcsRec]
      split_ifs with heq
      · -- x = y
        cases hx with
        | cons _ hsub_x =>
          -- s unchanged, hsub_x : s.Sublist xs
          cases hy with
          | cons _ hsub_y =>
            -- s.Sublist ys
            have := ihx s ys hsub_x hsub_y; omega
          | cons₂ _ hsub_y =>
            -- hy was s.Sublist (y :: ys), cons₂ means s = y :: s_tail, hsub_y : s_tail.Sublist ys
            -- Also hsub_x : (y :: s_tail).Sublist xs from the cons case of hx
            -- s_tail.Sublist xs:
            have h_tail_xs := List.Sublist.trans (List.sublist_cons_self _ _) hsub_x
            have := ihx _ ys h_tail_xs hsub_y
            simp_all [List.length_cons]
        | cons₂ _ hsub_x =>
          -- s = x :: s_tail, hsub_x : s_tail.Sublist xs
          cases hy with
          | cons _ hsub_y =>
            -- hsub_y : (x :: s_tail).Sublist ys
            have h_tail_ys := List.Sublist.trans (List.sublist_cons_self _ _) hsub_y
            have := ihx _ ys hsub_x h_tail_ys
            simp_all [List.length_cons]
          | cons₂ _ hsub_y =>
            -- s_tail.Sublist ys
            simp [List.length_cons]
            exact ihx _ ys hsub_x hsub_y
      · -- x ≠ y
        cases hx with
        | cons _ hsub =>
          calc s.length ≤ lcsRec xs (y :: ys) := ihx s (y :: ys) hsub hy
            _ ≤ Nat.max (lcsRec xs (y :: ys)) (lcsRec (x :: xs) ys) := Nat.le_max_left _ _
        | cons₂ _ hsub =>
          cases hy with
          | cons _ hsub2 =>
            have h1 := ihy _ (hsub.cons₂ x) hsub2
            exact le_trans h1 (Nat.le_max_right _ _)
          | cons₂ _ _ =>
            exact absurd rfl heq

-- Achievability: there exists a common sublist of length = lcsRec
lemma lcsRec_achievable (xs ys : List Int) :
    ∃ s : List Int, s.Sublist xs ∧ s.Sublist ys ∧ s.length = lcsRec xs ys := by
  induction xs generalizing ys with
  | nil => exact ⟨[], List.Sublist.slnil, List.nil_sublist _, by simp [lcsRec]⟩
  | cons x xs ihx =>
    induction ys with
    | nil => exact ⟨[], List.nil_sublist _, List.Sublist.slnil, by simp [lcsRec]⟩
    | cons y ys ihy =>
      simp only [lcsRec]
      split_ifs with heq
      · obtain ⟨s, hsx, hsy, hlen⟩ := ihx ys
        exact ⟨x :: s, hsx.cons₂ x, heq ▸ hsy.cons₂ y, by simp [hlen]⟩
      · by_cases h : lcsRec xs (y :: ys) ≥ lcsRec (x :: xs) ys
        · obtain ⟨s, hsx, hsy, hlen⟩ := ihx (y :: ys)
          exact ⟨s, hsx.cons x, hsy, by rw [hlen]; simp [Nat.max_def]; omega⟩
        · push_neg at h
          obtain ⟨s, hsx, hsy, hlen⟩ := ihy
          exact ⟨s, hsx, hsy.cons y, by rw [hlen]; simp [Nat.max_def]; omega⟩

-- Helper: characterize membership in the foldl that builds subsequences
private lemma mem_foldl_subseq (init : List (List Int)) (xs : List Int) (t : List Int) :
    t ∈ xs.foldl (fun acc x => acc ++ acc.map (fun sub => x :: sub)) init ↔
    ∃ s ∈ init, ∃ ys : List Int, ys.Sublist xs ∧ t = ys.reverse ++ s := by
  induction xs generalizing init with
  | nil =>
    simp only [List.foldl_nil]
    constructor
    · intro h; exact ⟨t, h, [], List.Sublist.slnil, by simp⟩
    · rintro ⟨s, hs, ys, hys, rfl⟩
      have := List.eq_nil_of_sublist_nil hys; subst this; simpa
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    constructor
    · rintro ⟨s, hs, ys, hys, rfl⟩
      simp only [List.mem_append, List.mem_map] at hs
      rcases hs with hs | ⟨s', hs', rfl⟩
      · exact ⟨s, hs, ys, hys.cons x, rfl⟩
      · refine ⟨s', hs', x :: ys, hys.cons₂ x, ?_⟩
        simp [List.reverse_cons]
    · rintro ⟨s, hs, ys, hys, rfl⟩
      cases hys with
      | cons _ hys' =>
        exact ⟨s, List.mem_append_left _ hs, ys, hys', rfl⟩
      | cons₂ _ hys' =>
        refine ⟨x :: s, List.mem_append_right _ (List.mem_map.mpr ⟨s, hs, rfl⟩), _, hys', ?_⟩
        simp [List.reverse_cons]

-- Bridge lemma: allSubseq generates exactly sublists
lemma mem_allSubseq_iff (arr : Array Int) (l : List Int) :
    l ∈ ((arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]]
      |>.map List.reverse) ↔ l.Sublist arr.toList := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [← Array.foldl_toList] at hs
    rw [mem_foldl_subseq] at hs
    obtain ⟨t, ht, ys, hys, rfl⟩ := hs
    simp only [List.mem_singleton] at ht; subst ht
    simpa [List.reverse_append] using hys
  · intro h
    refine ⟨l.reverse, ?_, List.reverse_reverse l⟩
    rw [← Array.foldl_toList]
    rw [mem_foldl_subseq]
    exact ⟨[], List.mem_singleton.mpr rfl, l, h, by simp⟩

-- ===== Pure recursive DP value (peels from back, matching DP recurrence) =====
private def lcsVal (a b : Array Int) : Nat → Nat → Int
  | 0, _ => 0
  | _, 0 => 0
  | i + 1, j + 1 =>
    if a[i]! = b[j]! then lcsVal a b i j + 1
    else intMax (lcsVal a b i (j + 1)) (lcsVal a b (i + 1) j)

-- ===== lcsVal = lcsRec (via reversal argument) =====
private lemma sublist_reverse' {l₁ l₂ : List Int}
    (h : l₁.Sublist l₂) : l₁.reverse.Sublist l₂.reverse := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih => simp only [List.reverse_cons]; exact ih.trans (List.sublist_append_left ..)
  | cons₂ a _ ih => simp only [List.reverse_cons]; exact ih.append (List.Sublist.refl [a])

private lemma lcsRec_rev (xs ys : List Int) :
    lcsRec xs ys = lcsRec xs.reverse ys.reverse := by
  apply Nat.le_antisymm
  · obtain ⟨s, hsx, hsy, hlen⟩ := lcsRec_achievable xs ys
    calc lcsRec xs ys = s.length := hlen.symm
      _ = s.reverse.length := by simp
      _ ≤ _ := lcsRec_optimal _ _ _ (sublist_reverse' hsx) (sublist_reverse' hsy)
  · obtain ⟨s, hsx, hsy, hlen⟩ := lcsRec_achievable xs.reverse ys.reverse
    have hsx' := sublist_reverse' hsx; have hsy' := sublist_reverse' hsy; simp at hsx' hsy'
    calc lcsRec xs.reverse ys.reverse = s.length := hlen.symm
      _ = s.reverse.length := by simp
      _ ≤ _ := lcsRec_optimal _ _ _ hsx' hsy'

private lemma take_succ_reverse' (l : List Int) (i : Nat) (h : i < l.length) :
    (l.take (i + 1)).reverse = l[i] :: (l.take i).reverse := by
  rw [List.take_succ, List.getElem?_eq_getElem h]; simp [List.reverse_append]

private lemma lcsVal_eq_rev (a b : Array Int) (i j : Nat) (hi : i ≤ a.size) (hj : j ≤ b.size) :
    lcsVal a b i j = ↑(lcsRec (a.toList.take i).reverse (b.toList.take j).reverse) := by
  induction i, j using lcsVal.induct a b with
  | case1 j => simp [lcsVal, lcsRec]
  | case2 i =>
    simp only [lcsVal]
    cases (a.toList.take i).reverse with
    | nil => simp [lcsRec]
    | cons _ _ => simp [lcsRec]
  | case3 i j heq ih =>
    have hi' : i < a.size := by omega
    have hj' : j < b.size := by omega
    rw [lcsVal, if_pos heq, take_succ_reverse' _ _ (by simp; omega),
        take_succ_reverse' _ _ (by simp; omega)]
    simp only [lcsRec]
    have ha : a[i]! = a.toList[i] := by
      rw [getElem!_pos a i hi']; simp
    have hb : b[j]! = b.toList[j] := by
      rw [getElem!_pos b j hj']; simp
    rw [ha, hb] at heq
    simp [heq]; exact ih (by omega) (by omega)
  | case4 i j heq ih1 ih2 =>
    have hi' : i < a.size := by omega
    have hj' : j < b.size := by omega
    rw [lcsVal, if_neg heq, take_succ_reverse' _ _ (by simp; omega),
        take_succ_reverse' _ _ (by simp; omega)]
    simp only [lcsRec]
    have ha : a[i]! = a.toList[i] := by
      rw [getElem!_pos a i hi']; simp
    have hb : b[j]! = b.toList[j] := by
      rw [getElem!_pos b j hj']; simp
    rw [ha, hb] at heq
    rw [if_neg heq, intMax_eq_max,
        ih1 (by omega) (by omega), ih2 (by omega) (by omega),
        take_succ_reverse' b.toList j (by simp; omega),
        take_succ_reverse' a.toList i (by simp; omega)]
    push_cast; norm_cast

private lemma lcsVal_eq_lcsRec' (a b : Array Int) (i j : Nat) (hi : i ≤ a.size) (hj : j ≤ b.size) :
    lcsVal a b i j = ↑(lcsRec (a.toList.take i) (b.toList.take j)) := by
  rw [lcsRec_rev]; exact lcsVal_eq_rev a b i j hi hj

-- ===== Array helper lemmas =====
private lemma gs_same {α : Type} [Inhabited α] (ar : Array α) (i : Nat) (v : α) (h : i < ar.size) :
    (ar.set! i v)[i]! = v := by
  have hsz : i < (ar.set! i v).size := by simp [Array.set!]; exact h
  rw [getElem!_pos (ar.set! i v) i hsz]; simp [Array.set!]

private lemma gs_diff {α : Type} [Inhabited α] (ar : Array α) (i j : Nat) (v : α)
    (hij : i ≠ j) (hj : j < ar.size) :
    (ar.set! i v)[j]! = ar[j]! := by
  have hsz : j < (ar.set! i v).size := by simp [Array.set!]; exact hj
  rw [getElem!_pos (ar.set! i v) j hsz, getElem!_pos ar j hj]
  simp only [Array.set!]; exact Array.getElem_setIfInBounds_ne hj hij

private lemma sz_set {α : Type} (ar : Array α) (i : Nat) (v : α) :
    (ar.set! i v).size = ar.size := by simp [Array.set!]

-- ===== Cell update =====
private def dpCell (a b : Array Int) (i j : Nat) (dp : Array (Array Int)) : Array (Array Int) :=
  if i = 0 ∨ j = 0 then dp
  else if a[i - 1]! = b[j - 1]! then
    dp.set! i (dp[i]!.set! j (((dp[i - 1]!)[j - 1]!) + 1))
  else
    dp.set! i (dp[i]!.set! j (intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)))

private lemma dpCell_base (a b : Array Int) (dp : Array (Array Int)) (i j : Nat)
    (h : i = 0 ∨ j = 0) : dpCell a b i j dp = dp := by unfold dpCell; simp [h]

private lemma dpCell_sz (a b : Array Int) (dp : Array (Array Int)) (i j : Nat) :
    (dpCell a b i j dp).size = dp.size := by unfold dpCell; split_ifs <;> simp [Array.set!]

private lemma dpCell_other_row (a b : Array Int) (dp : Array (Array Int)) (i j i' : Nat)
    (hi' : i' ≠ i) (hi'b : i' < dp.size) :
    ∀ (j' : Nat), ((dpCell a b i j dp)[i']!)[j']! = (dp[i']!)[j']! := by
  have key : (dpCell a b i j dp)[i']! = dp[i']! := by
    unfold dpCell; split_ifs <;> try rfl
    all_goals exact gs_diff dp i i' _ (Ne.symm hi') hi'b
  intro j'; rw [key]

private lemma dpCell_other_col (a b : Array Int) (dp : Array (Array Int)) (i j j' : Nat)
    (hj' : j' ≠ j) (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hib : i < dp.size)
    (hrsz : (dp[i]!).size = b.size + 1) (hjb : j ≤ b.size) (hj'b : j' ≤ b.size) :
    ((dpCell a b i j dp)[i]!)[j']! = (dp[i]!)[j']! := by
  unfold dpCell; rw [if_neg (show ¬(i = 0 ∨ j = 0) from by omega)]
  split_ifs <;> (rw [gs_same dp i _ hib, gs_diff _ j j' _ hj'.symm (by rw [hrsz]; omega)])

private lemma dpCell_rsz (a b : Array Int) (dp : Array (Array Int)) (i j : Nat)
    (hib : i < dp.size) (hjb : j ≤ b.size)
    (hrsz : ∀ r, r < dp.size → (dp[r]!).size = b.size + 1) :
    ∀ r, r < (dpCell a b i j dp).size → ((dpCell a b i j dp)[r]!).size = b.size + 1 := by
  intro r hr; rw [dpCell_sz] at hr
  by_cases hri : r = i
  · subst hri; unfold dpCell; split_ifs <;> try exact hrsz r hr
    all_goals (rw [gs_same dp r _ hr]; rw [sz_set]; exact hrsz r hr)
  · have heq : (dpCell a b i j dp)[r]! = dp[r]! := by
      unfold dpCell; split_ifs <;> try rfl
      all_goals exact gs_diff dp i r _ (Ne.symm hri) hr
    rw [heq]; exact hrsz r hr

private lemma dpCell_val (a b : Array Int) (dp : Array (Array Int)) (i j : Nat)
    (hi : 0 < i) (hj : 0 < j) (him : i ≤ a.size) (hjn : j ≤ b.size)
    (hsz : dp.size = a.size + 1)
    (hrsz : ∀ r, r < dp.size → (dp[r]!).size = b.size + 1)
    (h1 : (dp[i-1]!)[j-1]! = lcsVal a b (i-1) (j-1))
    (h2 : (dp[i-1]!)[j]! = lcsVal a b (i-1) j)
    (h3 : (dp[i]!)[j-1]! = lcsVal a b i (j-1)) :
    ((dpCell a b i j dp)[i]!)[j]! = lcsVal a b i j := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 h3
  unfold dpCell; rw [if_neg (show ¬(i' + 1 = 0 ∨ j' + 1 = 0) from by omega)]
  simp only [Nat.add_sub_cancel]
  rw [lcsVal]
  split_ifs with heq
  · rw [gs_same dp _ _ (by omega), gs_same _ _ _ (by rw [hrsz _ (by omega)]; omega), h1]
  · rw [gs_same dp _ _ (by omega), gs_same _ _ _ (by rw [hrsz _ (by omega)]; omega), h2, h3]

-- ===== Inner loop invariant =====
private lemma inner_inv (a b : Array Int) (dp₀ : Array (Array Int)) (i : Nat)
    (him : i ≤ a.size) (hsz : dp₀.size = a.size + 1)
    (hrsz : ∀ r, r < dp₀.size → (dp₀[r]!).size = b.size + 1)
    (hprev : ∀ i' j', i' < i → j' ≤ b.size → (dp₀[i']!)[j']! = lcsVal a b i' j')
    (hcurr0 : ∀ j', j' ≤ b.size → (dp₀[i]!)[j']! = 0)
    (k : Nat) (hk : k ≤ b.size + 1) :
    let dp := (List.range k).foldl (fun dp j => dpCell a b i j dp) dp₀
    dp.size = a.size + 1
    ∧ (∀ r, r < dp.size → (dp[r]!).size = b.size + 1)
    ∧ (∀ j', j' < k → j' ≤ b.size → (dp[i]!)[j']! = lcsVal a b i j')
    ∧ (∀ j', j' ≥ k → j' ≤ b.size → (dp[i]!)[j']! = 0)
    ∧ (∀ (i' j' : Nat), i' ≠ i → i' < dp₀.size → (dp[i']!)[j']! = (dp₀[i']!)[j']!) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨hsz, hrsz, ?_, ?_, ?_⟩
    · intro _ h; omega
    · intro j' _ hj'; exact hcurr0 j' hj'
    · exact fun _ _ _ _ => trivial
  | succ k ihk =>
    obtain ⟨sz_k, rsz_k, fill_k, zero_k, other_k⟩ := ihk (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set dp_k := (List.range k).foldl (fun dp j => dpCell a b i j dp) dp₀
    have sz_new := dpCell_sz a b dp_k i k
    refine ⟨by rw [sz_new, sz_k], ?_, ?_, ?_, ?_⟩
    · exact dpCell_rsz a b dp_k i k (by rw [sz_k]; omega) (by omega) rsz_k
    · intro j' hj' hjn'
      by_cases hjk : j' < k
      · by_cases h0 : i = 0 ∨ k = 0
        · rw [dpCell_base _ _ _ _ _ h0]; exact fill_k j' hjk hjn'
        · push_neg at h0
          rw [dpCell_other_col _ _ _ _ _ _ (by omega) h0.1 h0.2 (by rw [sz_k]; omega)
              (rsz_k i (by rw [sz_k]; omega)) (by omega) hjn']
          exact fill_k j' hjk hjn'
      · have hj'k : k = j' := by omega
        subst hj'k
        by_cases h0 : i = 0 ∨ k = 0
        · rw [dpCell_base _ _ _ _ _ h0, zero_k k (le_refl _) (by omega)]
          rcases h0 with rfl | rfl <;> (unfold lcsVal; split <;> first | rfl | omega)
        · push_neg at h0
          exact dpCell_val a b dp_k i k (by omega) (by omega) him (by omega) sz_k rsz_k
            (by rw [other_k _ _ (by omega) (by rw [hsz]; omega)]; exact hprev _ _ (by omega) (by omega))
            (by rw [other_k _ _ (by omega) (by rw [hsz]; omega)]; exact hprev _ _ (by omega) (by omega))
            (fill_k _ (by omega) (by omega))
    · intro j' hj' hjn'
      by_cases h0 : i = 0 ∨ k = 0
      · rw [dpCell_base _ _ _ _ _ h0]; exact zero_k j' (by omega) hjn'
      · push_neg at h0
        rw [dpCell_other_col _ _ _ _ _ _ (by omega) h0.1 h0.2 (by rw [sz_k]; omega)
            (rsz_k i (by rw [sz_k]; omega)) (by omega) hjn']
        exact zero_k j' (by omega) hjn'
    · intro i' j' hi' hi'b
      have h := dpCell_other_row a b dp_k i k i' hi' (by rw [sz_k, ← hsz]; exact hi'b) j'
      rw [h]; exact other_k i' j' hi' hi'b

-- ===== Outer loop invariant =====
private lemma outer_inv (a b : Array Int) (k : Nat) (hk : k ≤ a.size + 1) :
    let m := a.size; let n := b.size
    let dp := (List.range k).foldl (fun dp i =>
      (List.range (n + 1)).foldl (fun dp j => dpCell a b i j dp) dp
    ) (Array.mkArray (m + 1) (Array.mkArray (n + 1) (0 : Int)))
    dp.size = m + 1
    ∧ (∀ r, r < dp.size → (dp[r]!).size = n + 1)
    ∧ (∀ i j, i < k → j ≤ n → (dp[i]!)[j]! = lcsVal a b i j)
    ∧ (∀ i j, i ≥ k → i ≤ m → j ≤ n → (dp[i]!)[j]! = 0) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Array.mkArray]
    refine ⟨by simp, ?_, by omega, ?_⟩
    · intro r hr; simp at hr
      have hsz : r < (Array.replicate (a.size + 1) (Array.replicate (b.size + 1) (0 : Int))).size := by simp; omega
      rw [getElem!_pos _ r hsz]; simp
    · intro i j _ hi hj
      have hi' : i < (Array.replicate (a.size + 1) (Array.replicate (b.size + 1) (0 : Int))).size := by simp; omega
      rw [getElem!_pos _ i hi']; simp
      have hj' : j < (Array.replicate (b.size + 1) (0 : Int)).size := by simp; omega
      rw [getElem!_pos _ j hj']; simp
  | succ k ihk =>
    -- Express the (k+1)-step fold as inner fold applied to k-step fold
    set dp_k := (List.range k).foldl (fun dp i =>
      (List.range (b.size + 1)).foldl (fun dp j => dpCell a b i j dp) dp
    ) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) (0 : Int))) with h_dp_k
    have step : (List.range (k + 1)).foldl (fun dp i =>
        (List.range (b.size + 1)).foldl (fun dp j => dpCell a b i j dp) dp
      ) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) (0 : Int))) =
      (List.range (b.size + 1)).foldl (fun dp j => dpCell a b k j dp) dp_k := by
      rw [show List.range (k + 1) = List.range k ++ [k] from List.range_succ,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [step]
    obtain ⟨sz_k, rsz_k, fill_k, zero_k⟩ := ihk (by omega)
    simp only [← h_dp_k] at sz_k rsz_k fill_k zero_k
    have inner := inner_inv a b dp_k k (by omega) sz_k rsz_k
      (fun i' j' hi' hj' => fill_k i' j' hi' hj')
      (fun j' hj' => zero_k k j' (le_refl _) (by omega) hj')
      (b.size + 1) (le_refl _)
    obtain ⟨sz_f, rsz_f, fill_f, _, other_f⟩ := inner
    refine ⟨sz_f, rsz_f, ?_, ?_⟩
    · intro i' j' hi' hj'
      by_cases hik : i' < k
      · rw [other_f i' j' (by omega) (by rw [sz_k]; omega)]; exact fill_k i' j' hik hj'
      · have hieq : i' = k := by omega
        subst hieq; exact fill_f j' (by omega) hj'
    · intro i' j' hi' hi'b hj'
      rw [other_f i' j' (by omega) (by rw [sz_k]; omega)]
      exact zero_k i' j' (by omega) hi'b hj'

-- ===== Bridge: DP = nested foldl =====
private lemma dp_eq_foldl (a b : Array Int) :
    (Id.run do
      let mut dp := Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) (0 : Int))
      for i in List.range (a.size + 1) do
        for j in List.range (b.size + 1) do
          if i = 0 ∨ j = 0 then ()
          else if a[i - 1]! = b[j - 1]! then
            let newVal := ((dp[i - 1]!)[j - 1]!) + 1
            dp := dp.set! i (dp[i]!.set! j newVal)
          else
            let newVal := intMax ((dp[i - 1]!)[j]!) ((dp[i]!)[j - 1]!)
            dp := dp.set! i (dp[i]!.set! j newVal)
      return dp) =
    (List.range (a.size + 1)).foldl (fun dp i =>
      (List.range (b.size + 1)).foldl (fun dp j => dpCell a b i j dp) dp
    ) (Array.mkArray (a.size + 1) (Array.mkArray (b.size + 1) (0 : Int))) := by
  simp only [Id.run, dpCell, intMax, bind_pure_comp, Id.pure_eq, Id.map_eq, Id.bind_eq]
  simp only [List.forIn_yield_eq_foldl]
  simp only [← apply_ite ForInStep.yield]
  simp only [List.forIn_yield_eq_foldl]

-- Bridge lemma: DP computes lcsRec
lemma dp_computes_lcsRec (a b : Array Int) :
    LongestCommonSubsequence a b trivial = ↑(lcsRec a.toList b.toList) := by
  simp only [LongestCommonSubsequence]
  -- Convert the do-block to foldl
  rw [dp_eq_foldl]
  -- Now use outer_inv to show the foldl computes lcsVal
  have inv := outer_inv a b (a.size + 1) le_rfl
  obtain ⟨_, _, fill, _⟩ := inv
  rw [fill a.size b.size (by omega) le_rfl,
      lcsVal_eq_lcsRec' a b a.size b.size le_rfl le_rfl]
  have ha : a.toList.take a.size = a.toList := by simp
  have hb : b.toList.take b.size = b.toList := by simp
  rw [ha, hb]

/-- prove the following theorem, please note that native_decide class tactic is not allowed -/
theorem LongestCommonSubsequence_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : LongestCommonSubsequence_precond (a) (b)) :
    LongestCommonSubsequence_postcond (a) (b) (LongestCommonSubsequence (a) (b) h_precond) h_precond := by
  simp only [LongestCommonSubsequence_postcond]
  rw [dp_computes_lcsRec]
  constructor
  · -- Part 1: lcsRec length is achieved by some common subsequence
    obtain ⟨s, hsa, hsb, hlen⟩ := lcsRec_achievable a.toList b.toList
    rw [List.contains_iff]
    rw [List.mem_map]
    refine ⟨s, ?_, by exact_mod_cast hlen⟩
    rw [List.mem_filter]
    exact ⟨(mem_allSubseq_iff a s).mpr hsa,
           (List.contains_iff).mpr ((mem_allSubseq_iff b s).mpr hsb)⟩
  · -- Part 2: all common subsequence lengths ≤ lcsRec
    rw [List.all_eq_true]
    intro len hlen
    rw [List.mem_map] at hlen
    obtain ⟨s, hs_mem, rfl⟩ := hlen
    rw [List.mem_filter] at hs_mem
    obtain ⟨hs_a, hs_b⟩ := hs_mem
    rw [List.contains_iff] at hs_b
    have hsa := (mem_allSubseq_iff a s).mp hs_a
    have hsb := (mem_allSubseq_iff b s).mp hs_b
    simp only [decide_eq_true_eq]
    exact_mod_cast lcsRec_optimal s a.toList b.toList hsa hsb

end verina_advanced_2
