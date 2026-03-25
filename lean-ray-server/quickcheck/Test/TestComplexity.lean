/-
Test file for complexity analysis debugging
-/
import Quickcheck.Probe
import Lean

open Lean Meta Elab Term Quickcheck.Probe

-- Test: detect the exponential pattern in foldl
#check @List.foldl

-- Create a simple expression with the exponential pattern
def testExpr1 : MetaM Unit := do
  -- Pattern: fun acc x => acc ++ acc.map (fun sub => x :: sub)
  -- This is the classic subset generation pattern

  let listType := Expr.const ``List [.zero]
  let natType := Expr.const ``Nat []
  let listListNat := Expr.app listType (Expr.app listType natType)

  -- Build: fun acc x => acc ++ acc.map (fun sub => x :: sub)
  -- Using de Bruijn indices:
  --   acc is bvar 1 (inside the lambda fun x =>)
  --   x is bvar 0 (innermost)

  let inner := Expr.lam `acc listListNat
    (Expr.lam `x natType
      -- acc ++ acc.map (fun sub => x :: sub)
      -- simplified: just test detection of acc ++ acc.map f pattern
      (Expr.bvar 0)  -- placeholder
      .default)
    .default

  IO.println s!"Testing pattern detection..."

  -- Test the actual postcondition from verina_advanced_2
  -- let allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse

  -- We need to check if our pattern detection works
  IO.println "Detection test created"

-- Test with actual Expr from a definition
#check @Array.foldl

-- Define a test function that mimics the exponential pattern
def allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse

-- Now let's check if we can analyze this
#check allSubseq

-- Manual test of pattern detection
def testDetection : IO Unit := do
  IO.println "Testing exponential pattern detection..."

  -- Run in MetaM context
  let result ← Lean.Elab.runFrontend
    (input := "")
    (opts := {})
    (fileName := "test")
    (mainModuleName := `Test)

  IO.println s!"Result: completed"

-- Simple test: check if containsAccPlusAccMapPattern works
-- by examining the Expr structure

-- Helper to print Expr structure
partial def printExprStructure (e : Expr) (indent : Nat := 0) : MetaM Unit := do
  let indentStr := String.mk (List.replicate indent ' ')
  match e with
  | .bvar n => IO.println s!"{indentStr}bvar {n}"
  | .fvar id => IO.println s!"{indentStr}fvar {id.name}"
  | .mvar id => IO.println s!"{indentStr}mvar {id.name}"
  | .sort lvl => IO.println s!"{indentStr}sort {lvl}"
  | .const name _ => IO.println s!"{indentStr}const {name}"
  | .app fn arg =>
    IO.println s!"{indentStr}app:"
    printExprStructure fn (indent + 2)
    IO.println s!"{indentStr}  arg:"
    printExprStructure arg (indent + 4)
  | .lam name ty body _ =>
    IO.println s!"{indentStr}lam {name}:"
    IO.println s!"{indentStr}  ty:"
    printExprStructure ty (indent + 4)
    IO.println s!"{indentStr}  body:"
    printExprStructure body (indent + 4)
  | .forallE name ty body _ =>
    IO.println s!"{indentStr}forallE {name}:"
    printExprStructure ty (indent + 2)
    printExprStructure body (indent + 2)
  | .letE name ty val body _ =>
    IO.println s!"{indentStr}letE {name}:"
    IO.println s!"{indentStr}  ty:"
    printExprStructure ty (indent + 4)
    IO.println s!"{indentStr}  val:"
    printExprStructure val (indent + 4)
    IO.println s!"{indentStr}  body:"
    printExprStructure body (indent + 4)
  | .lit l => IO.println s!"{indentStr}lit {repr l}"
  | .mdata _ e =>
    IO.println s!"{indentStr}mdata:"
    printExprStructure e (indent + 2)
  | .proj name idx e =>
    IO.println s!"{indentStr}proj {name} {idx}"
    printExprStructure e (indent + 2)

-- Let's use #eval to test
#eval show MetaM Unit from do
  IO.println "Testing containsAccPlusAccMapPattern..."

  -- Get the constant info for allSubseq
  let env ← getEnv
  let some info := env.find? `allSubseq
    | throwError "allSubseq not found"

  let value := info.value!
  IO.println s!"allSubseq definition type: {info.type}"
  IO.println s!"\n=== Expr structure (first few levels) ===\n"

  -- Print simplified structure
  let rec printSimple (e : Expr) (depth : Nat) : IO Unit := do
    if depth > 6 then
      IO.println "..."
      return
    match e with
    | .bvar n => IO.println s!"bvar({n})"
    | .const name _ => IO.println s!"const({name})"
    | .app fn arg =>
      IO.print "app("
      printSimple fn (depth + 1)
      IO.print ", "
      printSimple arg (depth + 1)
      IO.println ")"
    | .lam name _ body _ =>
      IO.print s!"lam({name}, "
      printSimple body (depth + 1)
      IO.println ")"
    | _ => IO.println s!"{e.ctorName}"

  printSimple value 0

  IO.println s!"\n=== Looking for the fold function lambda ===\n"

  -- The structure should be:
  -- lam arr . (arr.foldl f init).map g
  -- We want to find f = fun acc x => acc ++ acc.map h

  -- Let's traverse and find lambdas
  let rec findLambdas (e : Expr) : IO (List Expr) := do
    match e with
    | .lam _ _ body _ =>
      let inner ← findLambdas body
      return e :: inner
    | .app fn arg =>
      let fnLams ← findLambdas fn
      let argLams ← findLambdas arg
      return fnLams ++ argLams
    | .letE _ _ val body _ =>
      let valLams ← findLambdas val
      let bodyLams ← findLambdas body
      return valLams ++ bodyLams
    | _ => return []

  let lambdas ← findLambdas value
  IO.println s!"Found {lambdas.length} lambda expressions"

  for (i, lam) in lambdas.enum do
    IO.println s!"\nLambda {i}:"
    printSimple lam 0

  -- Check for exponential pattern
  IO.println s!"\n=== Pattern detection ===\n"
  let hasExp ← detectExponentialPatterns value
  IO.println s!"Detected exponential pattern: {hasExp}"
