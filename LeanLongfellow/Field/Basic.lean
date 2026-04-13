import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Props
import Mathlib.Algebra.Field.ZMod

open Finset MultilinearPoly

/-! ## Instantiation for `ZMod p` (prime `p`)

Demonstrates that all definitions are computable over a concrete prime field.
Uses `ZMod 97` as a small example. -/

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- Example: 2-variable MLE over `ZMod 97`.
    Table: p(0,0) = 1, p(1,0) = 2, p(0,1) = 5, p(1,1) = 3.
    Extension: p(x,y) = 1·(1-x)(1-y) + 2·x(1-y) + 5·(1-x)·y + 3·x·y
              = 1 + x + 4y - 5xy -/
def examplePoly : MultilinearPoly (ZMod 97) 2 where
  table b :=
    match b 0, b 1 with
    | false, false => 1
    | true,  false => 2
    | false, true  => 5
    | true,  true  => 3

-- Test 1: Boolean point evaluation — all 4 corners of {0,1}² should return table values

example : examplePoly.eval (boolToField fun | 0 => false | 1 => false) = (1 : ZMod 97) := by
  native_decide

example : examplePoly.eval (boolToField fun | 0 => true | 1 => false) = (2 : ZMod 97) := by
  native_decide

example : examplePoly.eval (boolToField fun | 0 => false | 1 => true) = (5 : ZMod 97) := by
  native_decide

example : examplePoly.eval (boolToField fun | 0 => true | 1 => true) = (3 : ZMod 97) := by
  native_decide

-- Test 2: Extension evaluation:
-- p(x,y) = 1·(1-x)(1-y) + 2·x(1-y) + 5·(1-x)·y + 3·x·y = 1 + x + 4y - 3xy
-- p(2, 3) = 1 + 2 + 12 - 18 = -3 = 94 (mod 97)

example : examplePoly.eval (fun | 0 => 2 | 1 => 3) = (94 : ZMod 97) := by
  native_decide

-- Test 3: Hypercube sum: ∑ table = 1 + 2 + 5 + 3 = 11

example : (∑ b : Fin 2 → Bool, examplePoly.table b) = (11 : ZMod 97) := by
  native_decide

-- Test 4: Partial evaluation: fix x₀ = 3
-- partialEvalFirst fixes the first variable to 3:
-- table(false) = (1-3)·p(0,0) + 3·p(1,0) = (-2)·1 + 3·2 = -2 + 6 = 4
-- table(true)  = (1-3)·p(0,1) + 3·p(1,1) = (-2)·5 + 3·3 = -10 + 9 = -1 = 96 (mod 97)

example : (partialEvalFirst examplePoly (3 : ZMod 97)).table (fun _ => false) = (4 : ZMod 97) := by
  native_decide

example : (partialEvalFirst examplePoly (3 : ZMod 97)).table (fun _ => true) = (96 : ZMod 97) := by
  native_decide
