/-
Tests for the C-accelerated Quickcheck backend.

This file checks that the C random number generator behaves correctly.
-/

import Quickcheck.CGen

namespace Examples

open Quickcheck.CRng

/-- Test basic RNG output -/
def testBasic : IO Unit := do
  IO.println "Testing C RNG..."
  let rng := CRng.init 42
  let n1 := CRng.next rng
  let n2 := CRng.next rng
  IO.println s!"First random value: {n1}"
  IO.println s!"Second random value: {n2}"
  if n1 != n2 then
    IO.println "✓ RNG output looks normal"
  else
    IO.println "✗ RNG anomaly (two identical values)"

/-- Test Nat generation -/
def testNat : IO Unit := do
  IO.println "\nTesting Nat generation..."
  let rng := CRng.init 123
  for i in [0:5] do
    let n := genNat' rng 100
    IO.println s!"  Nat #{i+1} (0-100): {n}"

/-- Test Int generation -/
def testInt : IO Unit := do
  IO.println "\nTesting Int generation..."
  let rng := CRng.init 456
  for i in [0:5] do
    let n := genInt' rng (-50) 50
    IO.println s!"  Int #{i+1} (-50 to 50): {n}"

/-- Test Bool generation -/
def testBool : IO Unit := do
  IO.println "\nTesting Bool generation..."
  let rng := CRng.init 789
  let mut trueCount := 0
  let mut falseCount := 0
  for _ in [0:100] do
    if genBool rng then
      trueCount := trueCount + 1
    else
      falseCount := falseCount + 1
  IO.println s!"  True: {trueCount}, False: {falseCount}"

/-- Run all tests -/
def main : IO Unit := do
  testBasic
  testNat
  testInt
  testBool
  IO.println "\nAll tests finished."

-- Uncomment to run:
-- #eval main

end Examples
