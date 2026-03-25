import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_90


-- !benchmark @start solution_aux
@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
-- !benchmark @end precond_aux

@[reducible, simp]
def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (
    a.size = 0 ∨ (
      (List.range (a[0]!.size)).all (fun i =>
        List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
      )
    )
  )
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SlopeSearch (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) : (Int × Int) :=
  -- !benchmark @start code
  let rows := a.size
  let cols := if rows > 0 then (a[0]!).size else 0

  let rec aux (m n : Int) (fuel : Nat) : (Int × Int) :=
    if fuel = 0 then (-1, -1)
    else if m ≥ Int.ofNat rows || n < 0 then (-1, -1)
    else if get2d a m n = key then (m, n)
    else if get2d a m n < key then
      aux (m + 1) n (fuel - 1)
    else
      aux m (n - 1) (fuel - 1)

  aux 0 (Int.ofNat (cols - 1)) (rows + cols)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SlopeSearch_postcond (a : Array (Array Int)) (key : Int) (result: (Int × Int)) (h_precond : SlopeSearch_precond (a) (key)) :=
  -- !benchmark @start postcond
  let (m, n) := result;
  (m ≥ 0 ∧ m < a.size ∧ n ≥ 0 ∧ n < (a[0]!).size ∧ get2d a m n = key) ∨
  (m = -1 ∧ n = -1 ∧ a.all (fun x => x.all (fun e => e ≠ key)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SlopeSearch_spec_satisfied (a: Array (Array Int)) (key: Int) (h_precond : SlopeSearch_precond (a) (key)) :
    SlopeSearch_postcond (a) (key) (SlopeSearch (a) (key) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_90
