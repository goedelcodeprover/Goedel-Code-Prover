import Aesop
import Lean
import Std.Data.HashSet.Lemmas
import Tacs.UnfoldAll

open Lean Meta Elab Tactic
open Std
open UnfoldAll

set_option maxHeartbeats 0

namespace SimpGrindInduct

initialize registerTraceClass `simp_grind_induct

private def isInductiveConst (n : Name) : MetaM Bool := do
  match (← getEnv).find? n with
  | some (.inductInfo _) => return true
  | _ => return false

private def isInductiveType (e : Expr) : MetaM Bool := do
  let ty ← whnf (← inferType e)
  match ty.getAppFn with
  | .const n _ => isInductiveConst n
  | _          => return false

private def occursIn (mvar : MVarId) (fvar : FVarId) : MetaM Bool := do
  mvar.withContext do
    let tgt ← instantiateMVars (← mvar.getType)
    return tgt.occurs (.fvar fvar)

private structure InductCandidate where
  fvar : FVarId
  userName : Name
  priority : Nat
  occursScore : Nat
  index : Nat
deriving Inhabited

private def inductionTypePriority (ty : Expr) : MetaM Nat := do
  let ty ← whnf ty
  match ty.getAppFn with
  | .const name _ =>
      if name == ``Nat then
        return 4
      else if name == ``List then
        return 3
      else if name == ``Fin then
        return 2
      else if ← isInductiveConst name then
        return 1
      else
        return 0
  | _ => return 0

private def pickInductionCandidates (g : MVarId) : MetaM (Array InductCandidate) := do
  g.withContext do
    let mut cands : Array InductCandidate := #[]
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds do
      if let some decl := lctx.find? fvarId then
        if !decl.isAuxDecl then
          if ← isInductiveType (.fvar decl.fvarId) then
            let priority ← inductionTypePriority decl.type
            let occurs := (← occursIn g decl.fvarId).toNat
            let idx := cands.size
            cands := cands.push {
              fvar := decl.fvarId
              userName := decl.userName
              priority
              occursScore := occurs
              index := idx
            }
    let sorted := cands.qsort fun a b =>
      if a.priority == b.priority then
        if a.occursScore == b.occursScore then
          a.index < b.index
        else
          a.occursScore > b.occursScore
      else
        a.priority > b.priority
    return sorted

private def revertAllExcept (g : MVarId) (keep : FVarId) : MetaM (Array FVarId × MVarId) := do
  g.withContext do
    let mut others : Array FVarId := #[]
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds do
      if fvarId != keep then
        if let some decl := lctx.find? fvarId then
          if !decl.isAuxDecl then
            others := others.push decl.fvarId
    g.revert others

private def try0 : TacticM Unit := do
  try evalTactic (← `(tactic| try all_goals (first | rfl | (·aesop) | grind))) catch _ => pure ()

-- 定义 try0 作为 tactic，可以在 tactic 语法中使用
elab "try0" : tactic => do
  try0

private def InductGrindCore (simpIds : Array (TSyntax `ident)) : TacticM Unit := do
  let g0 ← getMainGoal
  let defNames := simpIds.map (fun stx => stx.getId)
  unfoldAllDefs defNames
  try try0 catch _ => pure ()

  if (← getUnsolvedGoals).isEmpty then return

  let cands ← pickInductionCandidates g0
  if cands.isEmpty then
    trace[simp_grind_induct] "no induction candidate found"
    return
  trace[simp_grind_induct] s!"pickInductionCandidates: {cands.size} candidates found: {cands.map (fun c => c.userName)}"

  let saved ← saveState
  let origGoals ← getGoals
  let mut succeeded := false
  for cand in cands do
    if succeeded then
      pure ()
    else do
      saved.restore
      setGoals origGoals
      let candName := cand.userName
      trace[simp_grind_induct] s!"trying induction on {candName}"
      let attempt ←
        try
          let (_, g1) ← revertAllExcept g0 cand.fvar
          replaceMainGoal [g1]
          let candIdent := mkIdent candName
          evalTactic (← `(tactic| induction $candIdent:ident with
                | nil =>
                  try0
                | cons _k _ks _ih =>
                  -- try first unfold_externall
                  try unfold_external_all at _ks
                  try split
                  try0
                  -- try second unfold_externall
                  try unfold_external_all at _ks
                  try split
                  try0
                  -- try unfold_internal_all
                  try unfold_internal_all at _ks
                  try split
                  try0))
          trace[simp_grind_induct] s!"induction {candIdent}, applied unfold_external_all and unfold_internal_all at _ks in cons branch"
          for g in (← getUnsolvedGoals) do
            trace[simp_grind_induct] (← g.withContext do
              return s!"current goal: {← ppExpr (← g.getType)}")
          for g in (← getUnsolvedGoals) do
            trace[simp_grind_induct] (← g.withContext do
            return s!"remaining goal: {← ppExpr (← g.getType)}")
          pure true
        catch _ =>
          pure false
      if attempt then
        succeeded := true
      else
        trace[simp_grind_induct] s!"induction on {candName} failed"

  unless succeeded do
    saved.restore
    setGoals origGoals
    trace[simp_grind_induct] "all induction candidates failed"
    return

syntax (name := inductGrindSyntax) "induct_grind" (ppSpace "[" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| induct_grind) =>
      InductGrindCore #[]
  | `(tactic| induct_grind [$defs,*]) => do
      InductGrindCore (defs.getElems)

end SimpGrindInduct

example (xs ys : List Nat) :
  (xs ++ ys).length = xs.length + ys.length := by
  grind

example (xs : List Int) (i : Int) (h : 0 ≤ i) :
  i.toNat < xs.length → (xs[i.toNat]?).isSome := by
  induct_grind
