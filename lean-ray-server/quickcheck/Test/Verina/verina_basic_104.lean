import Quickcheck
-- !benchmark @start import type=solution

-- !benchmark @end import

namespace verina_basic_104


-- !benchmark @start task_aux
structure Map (K V : Type) [BEq K] [BEq V] where
  entries : List (K × V)
deriving Inhabited

instance [BEq K] [BEq V] [Repr K] [Repr V] : Repr (Map K V) where
  reprPrec m _ := repr m.entries

instance [BEq K] [BEq V] [Quickcheck.Shrinkable K] [Quickcheck.Shrinkable V] : Quickcheck.Shrinkable (Map K V) where
  shrink m := (Quickcheck.Shrinkable.shrink m.entries).map (⟨·⟩)

instance [BEq K] [BEq V] [Quickcheck.Arbitrary K] [Quickcheck.Arbitrary V] : Quickcheck.Arbitrary (Map K V) where
  arbitrary := do
    let entries ← Quickcheck.Arbitrary.arbitrary (α := List (K × V))
    pure ⟨entries⟩

instance  (K V : Type) [BEq K] [BEq V] : BEq (Map K V) where
  beq m1 m2 := List.length m1.entries = List.length m2.entries ∧ List.beq m1.entries m2.entries

def empty {K V : Type} [BEq K] [BEq V] : Map K V := ⟨[]⟩

def insert {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) (v : V) : Map K V :=
  let entries := m.entries.filter (fun p => ¬(p.1 == k)) ++ [(k, v)]
  ⟨entries⟩

-- !benchmark @end task_aux

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def update_map (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  -- !benchmark @start code
  let foldFn := fun (acc : Map Int Int) (entry : Int × Int) =>
    insert acc entry.1 entry.2
  let updated := m2.entries.foldl foldFn m1
  ⟨updated.entries.mergeSort (fun a b => a.1 ≤ b.1)⟩
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)
-- !benchmark @end postcond_aux


@[reducible, simp]
def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem update_map_spec_satisfied (m1: Map Int Int) (m2: Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    update_map_postcond (m1) (m2) (update_map (m1) (m2) h_precond) h_precond := by
  -- !benchmark @start proof
  quickcheck (config := { Quickcheck.Configuration.adaptive with onlyDecidable := true, enableSafeNorm := true, quiet := true })

  -- !benchmark @end proof
end verina_basic_104
