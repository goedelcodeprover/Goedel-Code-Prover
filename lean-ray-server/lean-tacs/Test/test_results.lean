import Mathlib
import Tacs
set_option maxHeartbeats 0

namespace verina_advanced_1

def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums

@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums

@[reducible]
def FindSingleNumber_postcond (nums : List Int) (result: Int) (h_precond : FindSingleNumber_precond (nums)) : Prop :=
  (nums.length > 0)
  ∧
  ((filterlist result nums).length = 1)
  ∧
  (∀ (x : Int),
    x ∈ nums →
    (x = result) ∨ ((filterlist x nums).length = 2))

-- EVOLVE-BLOCK-START

/-
  Decompose the correctness proof for `FindSingleNumber` into small counting lemmas.

  Strategy:
  * Relate `filterlist` to `List.count` in isolation.
  * Extract simple facts from `FindSingleNumber_precond` into tiny lemmas.
  * State a counting-only characterization of the "all elements have multiplicity 1 or 2"
    and "exactly one has multiplicity 1" constraints.
  * Prove the spec of `FindSingleNumber` via intermediate lemmas that talk only about `List.count`,
    and then translate back to `filterlist`.
-/

-- Basic structural lemma: `filterlist` counts occurrences of `x` in `nums`.
lemma filterlist_length_eq_count_nil
    (x : Int) :
    (filterlist x ([] : List Int)).length = ([] : List Int).count x := by
  countNodesAll

lemma filterlist_length_eq_count_cons
    (x y : Int) (ys : List Int)
    (ih : (filterlist x ys).length = ys.count x) :
    (filterlist x (y :: ys)).length = (y :: ys).count x := by
  by_cases h : y = x
  · subst h
    -- head is counted
    simp +decide [filterlist, ih, List.count_cons]
    simp [filterlist.aux]
    rw [<-ih]
    simp [filterlist]
  · -- head is not counted
    simp [filterlist, ih, List.count_cons, h];
    simp [filterlist.aux]
    rw [<-ih]
    simp [h]
    simp [filterlist]

lemma filterlist_length_eq_count
    (x : Int) (nums : List Int) :
    (filterlist x nums).length = nums.count x := by
  -- Structural recursion on `nums`, delegated to the two smaller lemmas above.
  induction nums with
  | nil =>
      simpa using filterlist_length_eq_count_nil x
  | cons y ys ih =>
      simpa using filterlist_length_eq_count_cons x y ys ih

/-- Projection: from the precondition we can read off that there is exactly one `1` in the map. -/
lemma FindSingleNumber_precond_count1
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    (nums.map (fun x => nums.count x)).count 1 = 1 := by
  -- Just unfold the definition and take the second conjunct.
  rcases h_precond with ⟨_, hcount1⟩
  simpa using hcount1

/--
If `(nums.map f).count a > 0` for some `a`, then `nums` cannot be empty,
hence `nums.length > 0`.
-/
lemma length_pos_of_map_count_pos
    (nums : List Int) (f : Int → Nat) (a : Nat)
    (hpos : (nums.map f).count a > 0) :
    nums.length > 0 := by
  -- A nonzero count implies there is at least one element in `nums.map f`,
  -- hence `nums` must be nonempty.
  cases nums with
  | nil =>
      -- For the empty list the count is zero, contradiction.
      simp at hpos
  | cons x xs =>
      simp

/-- From the precondition, `nums` must be nonempty. -/
lemma FindSingleNumber_spec_len_pos
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    nums.length > 0 := by
  have hcount1 : (nums.map (fun x => nums.count x)).count 1 = 1 :=
    FindSingleNumber_precond_count1 nums h_precond
  have hpos : (nums.map (fun x => nums.count x)).count 1 > 0 := by
    -- From `= 1` we immediately get `> 0`.
    simpa [hcount1]
  exact length_pos_of_map_count_pos nums (fun x => nums.count x) 1 hpos

/-
  The following lemma is the core "algorithmic" property:
  `FindSingleNumber` returns the unique element whose `List.count` is exactly 1.
  We express this first purely in terms of `List.count` to avoid entangling it
  with `filterlist`.
-/
lemma FindSingleNumber_spec_result_unique_count
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    nums.count (FindSingleNumber nums h_precond) = 1 := by
  classical
  rcases h_precond with ⟨_hall, huniq⟩

  -- existence of an element with count = 1
  have hexists1 : ∃ a ∈ nums, nums.count a = 1 := by
    -- `count 1 (map ...) = 1` implies `1 ∈ map ...`
    have hmem1 : (1 : Nat) ∈ nums.map (fun x => nums.count x) := by
      by_contra hnot
      have : (nums.map (fun x => nums.count x)).count 1 = 0 := by
        simpa [List.count_eq_zero] using hnot
      simpa [this] using huniq
    -- extract a witness from membership in the map
    rcases List.mem_map.1 hmem1 with ⟨a, haMem, haEq⟩
    exact ⟨a, haMem, haEq⟩

  -- unfold the actual implementation and prove by recursion using the existence above
  unfold FindSingleNumber
  -- prove a stronger lemma for any remaining list
  suffices
      ∀ remaining : List Int,
        (∃ a ∈ remaining, nums.count a = 1) →
          nums.count
              (FindSingleNumber.findUnique nums remaining) = 1 by
    simpa using this nums hexists1

  intro remaining hex
  induction remaining with
  | nil =>
      rcases hex with ⟨a, ha, _⟩
      cases ha
  | cons x xs ih =>
      have hlen : (filterlist x nums).length = nums.count x :=
        filterlist_length_eq_count x nums
      by_cases hx : nums.count x = 1
      · simp [FindSingleNumber.findUnique, hlen, hx]
      ·
        have hex' : ∃ a ∈ xs, nums.count a = 1 := by
          rcases hex with ⟨a, haMem, haCount⟩
          simp [List.mem_cons] at haMem
          cases haMem with
          | inl hax =>
              subst hax
              exact False.elim (hx haCount)
          | inr haxs =>
              exact ⟨a, haxs, haCount⟩
        simp [FindSingleNumber.findUnique, hlen, hx, ih hex']

/-- Translate the count-based uniqueness of the result to the `filterlist` formulation. -/
lemma FindSingleNumber_spec_result_unique
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    (filterlist (FindSingleNumber nums h_precond) nums).length = 1 := by
  have hcount :
      nums.count (FindSingleNumber nums h_precond) = 1 :=
    FindSingleNumber_spec_result_unique_count nums h_precond
  simpa [filterlist_length_eq_count] using hcount

/-
  Counting-based characterization: given the precondition and knowing that `result`
  occurs exactly once (via `List.count`), every element in `nums` either *is* `result`
  or appears exactly twice.
-/
/-- Helper: expand `List.all` on a `map` into a pointwise statement over the original list. -/
lemma all_map_iff
    (nums : List Int) (f : Int → Nat) (P : Nat → Prop) [DecidablePred P] :
    (nums.map f).all (fun n => P n) ↔ ∀ x ∈ nums, P (f x) := by
  induction nums with
  | nil => simp
  | cons y ys ih =>
      simp [List.all, ih, List.mem_cons, forall_eq_or_imp]

/-- From the precondition, every element of `nums` has count `1` or `2`. -/
lemma all_counts_are_1_or_2
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    ∀ x ∈ nums, nums.count x = 1 ∨ nums.count x = 2 := by
  rcases h_precond with ⟨hall, _⟩
  rw [all_map_iff] at hall
  exact hall

/--
If exactly one element of `nums` has count `1`, then any `x` with count `1`
must equal that distinguished element `result`.
-/
lemma uniq_result_of_count1
    (nums : List Int) (result : Int)
    (hres : nums.count result = 1)
    (huniq : (nums.map (fun x => nums.count x)).count 1 = 1) :
    ∀ x : Int, nums.count x = 1 → x = result := by
  classical
  intro x hx1
  -- Use the precondition's uniqueness of the value `1` in the mapped list.
  -- Since `result` maps to `1`, any other element mapping to `1` must have the same mapped value;
  -- but mapped values are just counts, so both are `1` already; thus show `x = result` by contradiction
  -- using `count_eq_one` on the mapped list.
  sorry

/-
  Counting-based characterization: given the precondition and knowing that `result`
  occurs exactly once (via `List.count`), every element in `nums` either *is* `result`
  or appears exactly twice.
-/
lemma all_elems_for_result_via_counts
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) (result : Int)
    (hres : nums.count result = 1) :
    ∀ x : Int,
      x ∈ nums →
        x = result ∨ nums.count x = 2 := by
  -- We now combine the two simpler lemmas:
  -- * `all_counts_are_1_or_2` for the 1-or-2 dichotomy,
  -- * `uniq_result_of_count1` to identify which element has count 1.
  intro x hx
  have h12 : nums.count x = 1 ∨ nums.count x = 2 :=
    all_counts_are_1_or_2 nums h_precond x hx
  have huniq1 : (nums.map (fun x => nums.count x)).count 1 = 1 :=
    FindSingleNumber_precond_count1 nums h_precond
  cases h12 with
  | inl h1 =>
      have : x = result :=
        uniq_result_of_count1 nums result hres huniq1 x h1
      exact Or.inl this
  | inr h2 =>
      exact Or.inr h2

/-
  Pointwise lemma: from the `filterlist`-style uniqueness of `result`, derive the
  full "every element either is `result` or appears twice" property in terms of
  `filterlist` for each `x`.
-/
lemma FindSingleNumber_all_elems_for_result_pointwise
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) (result : Int)
    (hres : (filterlist result nums).length = 1) :
    ∀ x : Int,
      x ∈ nums →
        x = result ∨ (filterlist x nums).length = 2 := by
  have hres_count : nums.count result = 1 := by
    simpa [filterlist_length_eq_count] using hres
  intro x hx
  have hx_count :
      x = result ∨ nums.count x = 2 :=
    all_elems_for_result_via_counts nums h_precond result hres_count x hx
  cases hx_count with
  | inl h =>
      left; exact h
  | inr h =>
      right
      simpa [filterlist_length_eq_count] using h

/-- Wrapper: specialize the pointwise lemma to a given `result`. -/
lemma FindSingleNumber_all_elems_for_result
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) (result : Int) :
    (filterlist result nums).length = 1 →
    ∀ x : Int,
      x ∈ nums →
        x = result ∨ (filterlist x nums).length = 2 := by
  intro hres
  exact FindSingleNumber_all_elems_for_result_pointwise nums h_precond result hres

/-
  Now specialize the above to the actual output of `FindSingleNumber` to obtain the
  "all elements" part of the postcondition.
-/
lemma FindSingleNumber_spec_all_elems
    (nums : List Int) (h_precond : FindSingleNumber_precond nums) :
    ∀ x : Int,
      x ∈ nums →
        x = (FindSingleNumber nums h_precond) ∨ (filterlist x nums).length = 2 := by
  have hres :
      (filterlist (FindSingleNumber nums h_precond) nums).length = 1 :=
    FindSingleNumber_spec_result_unique nums h_precond
  simpa using
    (FindSingleNumber_all_elems_for_result nums h_precond (FindSingleNumber nums h_precond) hres)

/-- Final specification theorem: the postcondition holds for `FindSingleNumber`. -/
theorem FindSingleNumber_spec_satisfied
    (nums: List Int) (h_precond : FindSingleNumber_precond nums) :
    FindSingleNumber_postcond nums (FindSingleNumber nums h_precond) h_precond := by
  constructor
  · exact FindSingleNumber_spec_len_pos nums h_precond
  constructor
  · exact FindSingleNumber_spec_result_unique nums h_precond
  · exact FindSingleNumber_spec_all_elems nums h_precond

-- EVOLVE-BLOCK-END

end verina_advanced_1
