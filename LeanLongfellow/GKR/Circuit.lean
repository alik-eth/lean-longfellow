import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import Mathlib.Data.Fin.Tuple.Basic

open Finset MultilinearPoly

variable {F : Type*} [Field F] {k depth : ℕ}

-- ───────────────────────────────────────────────────────
-- Circuit types
-- ───────────────────────────────────────────────────────

/-- A layer's wiring predicate, represented as a multilinear polynomial
    over `3 * k` variables (gate index ++ left input ++ right input). -/
structure LayerQuad (F : Type*) [Field F] (k : ℕ) where
  quad : MultilinearPoly F (3 * k)

/-- Wire values at a single layer — a multilinear polynomial on `k` variables. -/
abbrev WireValues (F : Type*) [Field F] (k : ℕ) := MultilinearPoly F k

/-- A layered arithmetic circuit with uniform width `2^k` and `depth` layers. -/
structure LayeredCircuit (F : Type*) [Field F] (k : ℕ) (depth : ℕ) where
  quads : Fin depth → LayerQuad F k
  wires : Fin (depth + 1) → WireValues F k

-- ───────────────────────────────────────────────────────
-- Consistency predicates
-- ───────────────────────────────────────────────────────

/-- Layer `j` is consistent at gate `g` when the wire value equals the
    quadratic sum over all (left, right) input pairs. -/
def layerConsistentAt (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (g : Fin k → F) : Prop :=
  (circuit.wires (Fin.castSucc j)).eval g =
  ∑ b_lr : Fin (2 * k) → Bool,
    let lr_field := boolToField (F := F) b_lr
    let l : Fin k → F := fun i => lr_field (Fin.cast (by omega) (Fin.castAdd k i))
    let r : Fin k → F := fun i => lr_field (Fin.cast (by omega) (Fin.natAdd k i))
    let glr : Fin (3 * k) → F := fun i =>
      if h : i.val < k then g ⟨i.val, h⟩
      else lr_field ⟨i.val - k, by omega⟩
    (circuit.quads j).quad.eval glr *
    (circuit.wires ⟨j.val + 1, by omega⟩).eval l *
    (circuit.wires ⟨j.val + 1, by omega⟩).eval r

/-- Layer `j` is consistent for every Boolean gate index. -/
def layerConsistent (circuit : LayeredCircuit F k depth) (j : Fin depth) : Prop :=
  ∀ g : Fin k → Bool, layerConsistentAt circuit j (boolToField g)

/-- A circuit is valid when every layer is consistent and the output layer
    evaluates to zero on all Boolean inputs. -/
def circuitValid (circuit : LayeredCircuit F k depth) : Prop :=
  (∀ j, layerConsistent circuit j) ∧
  (∀ g : Fin k → Bool, (circuit.wires 0).eval (boolToField g) = 0)
