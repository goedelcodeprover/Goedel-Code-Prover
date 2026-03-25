import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_54


-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CanyonSearch_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0 ∧ List.Pairwise (· ≤ ·) a.toList ∧ List.Pairwise (· ≤ ·) b.toList
  -- !benchmark @end precond


-- !benchmark @start code_aux
def canyonSearchAux (a : Array Int) (b : Array Int) (m n d : Nat) : Nat :=
  if m < a.size ∧ n < b.size then
    let diff : Nat := ((a[m]! - b[n]!).natAbs)
    let new_d := if diff < d then diff else d
    if a[m]! <= b[n]! then
      canyonSearchAux a b (m + 1) n new_d
    else
      canyonSearchAux a b m (n + 1) new_d
  else
    d
termination_by a.size + b.size - m - n
-- !benchmark @end code_aux


def CanyonSearch (a : Array Int) (b : Array Int) (h_precond : CanyonSearch_precond (a) (b)) : Nat :=
  -- !benchmark @start code
  let init : Nat :=
    if a[0]! < b[0]! then (b[0]! - a[0]!).natAbs
    else (a[0]! - b[0]!).natAbs
  canyonSearchAux a b 0 0 init
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def CanyonSearch_postcond (a : Array Int) (b : Array Int) (result: Nat) (h_precond : CanyonSearch_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a.any (fun ai => b.any (fun bi => result = (ai - bi).natAbs))) ∧
  (a.all (fun ai => b.all (fun bi => result ≤ (ai - bi).natAbs)))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem CanyonSearch_spec_satisfied (a: Array Int) (b: Array Int) (h_precond : CanyonSearch_precond (a) (b)) :
    CanyonSearch_postcond (a) (b) (CanyonSearch (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_54
