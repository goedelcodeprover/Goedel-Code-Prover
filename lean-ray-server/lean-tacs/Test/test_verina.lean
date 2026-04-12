import Mathlib
import Tacs
set_option maxHeartbeats 0

namespace verina_advanced_60

@[reducible]
def partitionEvensOdds_precond (nums : List Nat) : Prop :=
  True

def partitionEvensOdds (nums : List Nat) (h_precond : partitionEvensOdds_precond (nums)) : (List Nat × List Nat) :=
  let rec helper (nums : List Nat) : (List Nat × List Nat) :=
    match nums with
    | [] => ([], [])
    | x :: xs =>
      let (evens, odds) := helper xs
      if x % 2 == 0 then (x :: evens, odds)
      else (evens, x :: odds)
  helper nums

@[reducible]
def partitionEvensOdds_postcond (nums : List Nat) (result: (List Nat × List Nat)) (h_precond : partitionEvensOdds_precond (nums)): Prop :=
  let evens := result.fst
  let odds := result.snd
  evens ++ odds = nums.filter (fun n => n % 2 == 0) ++ nums.filter (fun n => n % 2 == 1) ∧
  evens.all (fun n => n % 2 == 0) ∧
  odds.all (fun n => n % 2 == 1)

lemma partitionEvensOdds_fst_eq_filter (nums : List Nat)
    (h : partitionEvensOdds_precond nums) :
    (partitionEvensOdds nums h).fst = nums.filter (fun n => n % 2 == 0) := by
    unfold partitionEvensOdds List.filter
    induction nums with
    | nil =>
    -- simp_all only [List.filter_nil]
    rfl
    | cons x xs ih =>
      -- simp only [List.filter]
      extract_defs
      unfold partitionEvensOdds.helper
      -- simp only [partitionEvensOdds.helper]
      split
      grind

lemma partitionEvensOdds_snd_eq_filter (nums : List Nat)
    (h : partitionEvensOdds_precond nums) :
    (partitionEvensOdds nums h).snd = nums.filter (fun n => n % 2 == 1) := by
    -- simp_grind_induct [partitionEvensOdds, partitionEvensOdds.helper, List.filter]
    -- unfold partitionEvensOdds.helper
    unfold partitionEvensOdds
    induction nums with
    | nil => aesop
    | cons x xs ih =>
      simp only [List.filter]
      simp only [partitionEvensOdds.helper]
      split
      · grind
      · grind

lemma all_filter (l : List Nat) (p : Nat → Bool) :
    (l.filter p).all p = true := by
  simp_grind_induct

theorem partitionEvensOdds_spec_satisfied (nums : List Nat)
    (h_precond : partitionEvensOdds_precond nums) :
    partitionEvensOdds_postcond nums
      (partitionEvensOdds nums h_precond) h_precond := by
  unfold partitionEvensOdds_postcond
  have hfst := partitionEvensOdds_fst_eq_filter nums h_precond
  have hsnd := partitionEvensOdds_snd_eq_filter nums h_precond
  simpa [hfst, hsnd, all_filter] using
    (by
      triv)

end verina_advanced_60
