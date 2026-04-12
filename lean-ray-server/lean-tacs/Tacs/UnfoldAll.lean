import Lean
import Tacs.ExtractDefs

open Lean Meta Elab Tactic
open ExtractDefs

namespace UnfoldAll

-- 在所有目标和假设上展开定义列表
def unfoldAllDefs (defNames : Array Name) : TacticM Unit := do
  if defNames.isEmpty then
    return

  -- 将名称转换为 ident 语法
  let idents := defNames.map (fun n => mkIdent n)

  -- 构建 unfold 语法：逐个展开每个定义
  for ident in idents do
    -- 在所有目标上展开当前定义
    try evalTactic (← `(tactic| all_goals unfold $ident:ident)) catch _ => pure ()

  -- 使用 simp_all 在假设上也展开所有定义
  if !idents.isEmpty then
    let args := idents
    try evalTactic (← `(tactic| all_goals simp_all (config := { unfoldPartialApp := true }) only [$[$args:ident],*])) catch _ => pure ()

-- 从 extract_defs 获取定义并展开
elab "unfold_all" : tactic => do
  let g ← getMainGoal
  let defs ← extractDefsFromGoal g
  if defs.isEmpty then
    logInfo "未找到任何定义可展开"
  else
    unfoldAllDefs defs

-- 展开所有内部定义（Lean 标准库中的定义）
elab "unfold_internal_all" : tactic => do
  let g ← getMainGoal
  let defs ← extractExternalDefsFromGoal g
  if defs.isEmpty then
    logInfo "未找到任何内部定义可展开"
  else
    unfoldAllDefs defs

-- 展开所有外部定义（用户本地定义）
elab "unfold_external_all" : tactic => do
  let g ← getMainGoal
  let defs ← extractLocalDefsFromGoal g
  if defs.isEmpty then
    logInfo "未找到任何外部定义可展开"
  else
    unfoldAllDefs defs

-- 从指定标识符中提取定义并展开
elab "unfold_all" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何定义可展开"
  else
    unfoldAllDefs defs

-- 从指定标识符中提取内部定义并展开
elab "unfold_internal_all" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractExternalDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何内部定义可展开"
  else
    unfoldAllDefs defs

-- 从指定标识符中提取外部定义并展开
elab "unfold_external_all" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractLocalDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何外部定义可展开"
  else
    unfoldAllDefs defs

-- 手动指定要展开的定义列表
syntax (name := unfoldAllSyntax) "unfold_all" "[" ident,* "]" : tactic

elab_rules : tactic
  | `(tactic| unfold_all [$defs,*]) => do
      let defNames := defs.getElems.map (fun stx => stx.getId)
      unfoldAllDefs defNames

end UnfoldAll
