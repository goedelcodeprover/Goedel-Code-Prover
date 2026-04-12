import Lean
import Std.Data.HashSet

open Lean Meta Elab Tactic
open Std

namespace ExtractDefs

-- 收集表达式中所有常量名称
private def collectConsts (e : Expr) : HashSet Name :=
  let rec visit (e : Expr) (acc : HashSet Name) : HashSet Name :=
    match e with
    | .const n _ => acc.insert n
    | .app f a => visit a (visit f acc)
    | .lam _ _ b _ => visit b acc
    | .forallE _ _ b _ => visit b acc
    | .letE _ _ v b _ => visit b (visit v acc)
    | .mdata _ e => visit e acc
    | .proj _ _ e => visit e acc
    | _ => acc
  visit e {}

-- 检查一个名称是否是定义（def）
private def isDef (n : Name) : MetaM Bool := do
  match (← getEnv).find? n with
  | some (.defnInfo _) => return true
  | _ => return false

-- 检查名称是否是内部生成的函数（如 match_1 等, 这些在Lean中无法直接定义）
private def isInternalGenerated (n : Name) : Bool :=
  let rec checkComponents (name : Name) : Bool :=
    match name with
    | .str parent str =>
      (str.startsWith "match_" ||
       str.startsWith "_") || checkComponents parent
    | .num parent _ => checkComponents parent
    | _ => false
  checkComponents n

-- 检查名称是否应该保留（Array、List 或本地命名空间）
private def shouldKeep (n : Name) : MetaM Bool := do
  -- 排除内部生成的函数
  if isInternalGenerated n then
    return false
  -- 获取当前命名空间
  let currNamespace ← getCurrNamespace
  -- 检查名称的第一个组件是否是 Array 或 List
  let firstComponent := n.getRoot
  if firstComponent == `Array || firstComponent == `List then
    return true
  -- 如果当前命名空间不是匿名的，检查名称是否在当前命名空间下
  if currNamespace != Name.anonymous then
    if currNamespace.isPrefixOf n then
      return true
  return false

-- 检查名称是否是本地定义（在当前命名空间下）
private def isLocalDef (n : Name) : MetaM Bool := do
  -- 排除内部生成的函数
  if isInternalGenerated n then
    return false
  -- 获取当前命名空间
  let currNamespace ← getCurrNamespace
  -- 如果当前命名空间不是匿名的，检查名称是否在当前命名空间下
  if currNamespace != Name.anonymous then
    if currNamespace.isPrefixOf n then
      return true
  return false

-- 检查名称是否是 Lean 内部/外部定义（标准库中的定义，如 List、Array 等）
private def isExternalDef (n : Name) : MetaM Bool := do
  -- 排除内部生成的函数
  if isInternalGenerated n then
    return false
  -- 获取当前命名空间
  let currNamespace ← getCurrNamespace
  -- 检查名称的第一个组件是否是 Array 或 List
  let firstComponent := n.getRoot
  if firstComponent == `Array || firstComponent == `List then
    return true
  -- 如果名称不在当前命名空间下，且是标准库中的定义，则认为是外部定义
  if currNamespace != Name.anonymous then
    if !currNamespace.isPrefixOf n then
      -- 检查是否是标准库中的定义（通常以 Lean、Init、Std 等开头）
      let root := n.getRoot
      if root == `Lean || root == `Init || root == `Std then
        return true
  else
    -- 如果没有当前命名空间，检查是否是标准库中的定义
    let root := n.getRoot
    if root == `Lean || root == `Init || root == `Std || root == `Array || root == `List then
      return true
  return false

-- 从指定的 fvarId 中提取所有定义名称
-- 不仅从变量的类型中提取，还从目标表达式中提取与该变量相关的定义
def extractDefsFromFVar (fvarId : FVarId) (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    let mut allConsts : HashSet Name := {}

    -- 收集该变量的类型中的常量
    let lctx ← getLCtx
    if let some decl := lctx.find? fvarId then
      let declType ← instantiateMVars decl.type
      allConsts := collectConsts declType

    -- 收集目标表达式中与该变量相关的常量
    -- 检查目标表达式中是否包含该变量
    let tgt ← instantiateMVars (← g.getType)
    if tgt.containsFVar fvarId then
      let tgtConsts := collectConsts tgt
      allConsts := tgtConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出定义，并且只保留 Array、List 或本地命名空间的
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← shouldKeep constName then
          defs := defs.push constName
    return defs

-- 从指定的 fvarId 中提取本地定义（在当前命名空间下）
def extractLocalDefsFromFVar (fvarId : FVarId) (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    let mut allConsts : HashSet Name := {}

    -- 收集该变量的类型中的常量
    let lctx ← getLCtx
    if let some decl := lctx.find? fvarId then
      let declType ← instantiateMVars decl.type
      allConsts := collectConsts declType

    -- 收集目标表达式中与该变量相关的常量
    let tgt ← instantiateMVars (← g.getType)
    if tgt.containsFVar fvarId then
      let tgtConsts := collectConsts tgt
      allConsts := tgtConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出本地定义
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← isLocalDef constName then
          defs := defs.push constName
    return defs

-- 从指定的 fvarId 中提取外部定义（Lean 标准库中的定义）
def extractExternalDefsFromFVar (fvarId : FVarId) (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    let mut allConsts : HashSet Name := {}

    -- 收集该变量的类型中的常量
    let lctx ← getLCtx
    if let some decl := lctx.find? fvarId then
      let declType ← instantiateMVars decl.type
      allConsts := collectConsts declType

    -- 收集目标表达式中与该变量相关的常量
    let tgt ← instantiateMVars (← g.getType)
    if tgt.containsFVar fvarId then
      let tgtConsts := collectConsts tgt
      allConsts := tgtConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出外部定义
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← isExternalDef constName then
          defs := defs.push constName
    return defs

-- 从目标中提取所有定义名称
def extractDefsFromGoal (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    -- 收集目标中的常量
    let tgt ← instantiateMVars (← g.getType)
    let mut allConsts := collectConsts tgt

    -- 收集上下文中所有声明的类型中的常量
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds do
      if let some decl := lctx.find? fvarId then
        if !decl.isAuxDecl then
          let declType ← instantiateMVars decl.type
          let declConsts := collectConsts declType
          allConsts := declConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出定义，并且只保留 Array、List 或本地命名空间的
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← shouldKeep constName then
          defs := defs.push constName
    return defs

-- 从目标中提取本地定义（用户定义）
def extractLocalDefsFromGoal (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    -- 收集目标中的常量
    let tgt ← instantiateMVars (← g.getType)
    let mut allConsts := collectConsts tgt

    -- 收集上下文中所有声明的类型中的常量
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds do
      if let some decl := lctx.find? fvarId then
        if !decl.isAuxDecl then
          let declType ← instantiateMVars decl.type
          let declConsts := collectConsts declType
          allConsts := declConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出本地定义
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← isLocalDef constName then
          defs := defs.push constName
    return defs

-- 从目标中提取外部定义（Lean 标准库中的定义）
def extractExternalDefsFromGoal (g : MVarId) : MetaM (Array Name) := do
  g.withContext do
    -- 收集目标中的常量
    let tgt ← instantiateMVars (← g.getType)
    let mut allConsts := collectConsts tgt

    -- 收集上下文中所有声明的类型中的常量
    let lctx ← getLCtx
    for fvarId in lctx.getFVarIds do
      if let some decl := lctx.find? fvarId then
        if !decl.isAuxDecl then
          let declType ← instantiateMVars decl.type
          let declConsts := collectConsts declType
          allConsts := declConsts.fold (fun acc n => acc.insert n) allConsts

    -- 过滤出外部定义
    let mut defs : Array Name := #[]
    for constName in allConsts do
      if ← isDef constName then
        if ← isExternalDef constName then
          defs := defs.push constName
    return defs

-- 打印所有提取的定义
elab "extract_defs" : tactic => do
  let g ← getMainGoal
  let defs ← extractDefsFromGoal g
  if defs.isEmpty then
    logInfo "未找到任何定义"
  else
    let defsStr := defs.map toString |>.toList |> String.intercalate ", "
    logInfo s!"找到的定义: {defsStr}"

-- 从指定标识符中提取内部定义（Lean 标准库中的定义）
elab "extract_internal_defs" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractExternalDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何内部定义"
  else
    let defsStr := defs.map toString |>.toList |> String.intercalate ", "
    logInfo s!"在 {ident.getId} 中找到的内部定义: {defsStr}"

-- 从指定标识符中提取外部定义（用户本地定义）
elab "extract_external_defs" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractLocalDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何外部定义"
  else
    let defsStr := defs.map toString |>.toList |> String.intercalate ", "
    logInfo s!"在 {ident.getId} 中找到的外部定义: {defsStr}"

-- 从指定标识符中提取定义
elab "extract_defs" "at" ident:ident : tactic => do
  let g ← getMainGoal
  let fvarId ← Tactic.getFVarId ident
  let defs ← extractDefsFromFVar fvarId g
  if defs.isEmpty then
    logInfo s!"在 {ident.getId} 中未找到任何定义"
  else
    let defsStr := defs.map toString |>.toList |> String.intercalate ", "
    logInfo s!"在 {ident.getId} 中找到的定义: {defsStr}"

end ExtractDefs
