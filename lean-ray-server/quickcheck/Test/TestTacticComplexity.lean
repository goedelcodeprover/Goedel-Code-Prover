/-
Direct test of complexity analysis in tactic context
-/
import Quickcheck
import Quickcheck.Probe

open Lean Meta Elab Tactic Term Quickcheck.Probe

-- Define the exponential function
def allSubseq (arr : Array Int) := (arr.foldl fun acc x => acc ++ acc.map (fun sub => x :: sub)) [[]] |>.map List.reverse

-- Simple postcondition using allSubseq
@[reducible]
def testPostcond (a : Array Int) : Prop :=
  let subseqA := allSubseq a
  subseqA.length > 0

-- Test the analysis
#eval show MetaM Unit from do
  IO.println "=== Testing complexity analysis in tactic-like context ==="

  -- Get the type of the postcondition
  let env ← getEnv

  -- Construct expression: testPostcond a
  -- where a is a free variable of type Array Int
  let arrayIntType := Expr.app (Expr.const ``Array [.zero]) (Expr.const ``Int [])

  withLocalDecl `a .default arrayIntType fun aFVar => do
    -- Create the postcondition application
    let postcondExpr := Expr.app (Expr.const ``testPostcond []) aFVar

    IO.println s!"Testing expression: testPostcond a"

    -- Get the type
    let postcondType ← inferType postcondExpr
    IO.println s!"Type: {postcondType}"

    -- Expand with reducible transparency (like in tactic)
    let expanded ← withTransparency .reducible do
      whnf postcondExpr

    IO.println s!"Expanded (whnf): {expanded}"

    -- Now test detection
    let hasExp ← detectExponentialPatterns expanded
    IO.println s!"Detected exponential pattern: {hasExp}"

    -- Also test on the constant definition itself
    if let some info := env.find? ``allSubseq then
      let value := info.value!
      let hasExpInDef ← detectExponentialPatterns value
      IO.println s!"allSubseq definition has exponential pattern: {hasExpInDef}"

    -- Test recommendMaxSize
    let fvarId := aFVar.fvarId!
    let inputVars := #[(fvarId, `a)]
    let recommended ← recommendMaxSize expanded inputVars
    IO.println s!"Recommended maxSize: {recommended}"

    let debugInfo ← debugAnalysis expanded inputVars
    IO.println debugInfo

-- Simple quickcheck test with very low maxSize to verify it works
set_option trace.quickcheck true in
example : ∀ x : Nat, x + 0 = x := by
  quickcheck (config := { Quickcheck.Configuration.normal with maxSize := 10, numInst := 5 })
  sorry
