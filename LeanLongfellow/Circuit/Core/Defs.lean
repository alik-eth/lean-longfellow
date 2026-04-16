import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval

open Finset MultilinearPoly

variable {F : Type*} [Field F] {s : ℕ}

/-! # Layered Circuit Model

Defines the abstract functional representation of a layered arithmetic circuit.
Each layer's structure is encoded via multilinear polynomials `add_poly` and
`mul_poly` over 3s variables (g, l, r). Layer values are multilinear extensions.
-/

-- ============================================================
-- Section 1: Vector splitting and concatenation helpers
-- ============================================================

/-- Extract the first s components from a 2s-vector. -/
def splitL {s : ℕ} {α : Type*} (lr : Fin (2 * s) → α) : Fin s → α :=
  fun j => lr ⟨j.val, by omega⟩

/-- Extract the last s components from a 2s-vector. -/
def splitR {s : ℕ} {α : Type*} (lr : Fin (2 * s) → α) : Fin s → α :=
  fun j => lr ⟨j.val + s, by omega⟩

/-- Concatenate three s-vectors into one 3s-vector. -/
def concat3 {s : ℕ} {α : Type*} (g l r : Fin s → α) : Fin (3 * s) → α :=
  fun k =>
    if h : k.val < s then g ⟨k.val, h⟩
    else if h2 : k.val < 2 * s then l ⟨k.val - s, by omega⟩
    else r ⟨k.val - 2 * s, by omega⟩

-- ============================================================
-- Section 2: Circuit layer types
-- ============================================================

/-- A single layer's structure, encoded as multilinear polynomials.
    `s` is the number of index bits (layer has 2^s gates).
    `add_poly(g,l,r) = 1` iff gate g is an add gate with inputs (l,r).
    `mul_poly(g,l,r) = 1` iff gate g is a mul gate with inputs (l,r). -/
structure CircuitLayer (F : Type*) [Field F] (s : ℕ) where
  add_poly : MultilinearPoly F (3 * s)
  mul_poly : MultilinearPoly F (3 * s)

/-- Layer values as a multilinear extension. -/
abbrev LayerValues (F : Type*) [Field F] (s : ℕ) := MultilinearPoly F s

-- ============================================================
-- Section 3: Layer consistency
-- ============================================================

/-- Layer i's value at gate g equals the sum over all (l,r) pairs:
    V_i(g) = ∑_{l,r} add(g,l,r)·(V_{i+1}(l) + V_{i+1}(r))
                    + mul(g,l,r)·V_{i+1}(l)·V_{i+1}(r) -/
def layerConsistent (layer : CircuitLayer F s) (V_curr V_next : LayerValues F s)
    (g : Fin s → Bool) : Prop :=
  V_curr.table g = ∑ lr : Fin (2 * s) → Bool,
    let l := splitL lr
    let r := splitR lr
    layer.add_poly.table (concat3 g l r) * (V_next.table l + V_next.table r) +
    layer.mul_poly.table (concat3 g l r) * (V_next.table l * V_next.table r)

-- ============================================================
-- Section 4: Concatenation lemmas
-- ============================================================

@[simp] theorem concat3_left {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) (h : j.val < s := j.isLt) :
    concat3 g l r ⟨j.val, by omega⟩ = g j := by
  simp [concat3, h]

@[simp] theorem concat3_mid {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) :
    concat3 g l r ⟨j.val + s, by omega⟩ = l j := by
  simp only [concat3]
  have h1 : ¬(j.val + s < s) := by omega
  have h2 : j.val + s < 2 * s := by omega
  simp [h1, h2, show j.val + s - s = j.val by omega]

@[simp] theorem concat3_right {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) :
    concat3 g l r ⟨j.val + 2 * s, by omega⟩ = r j := by
  simp only [concat3]
  have h1 : ¬(j.val + 2 * s < s) := by omega
  have h2 : ¬(j.val + 2 * s < 2 * s) := by omega
  simp [h1, h2, show j.val + 2 * s - 2 * s = j.val by omega]

/-- boolToField commutes with concat3. -/
theorem concat3_boolToField {s : ℕ} {F : Type*} [Field F] (g l r : Fin s → Bool) :
    concat3 (boolToField (F := F) g) (boolToField l) (boolToField r) =
    boolToField (concat3 g l r) := by
  funext k
  simp only [concat3, boolToField]
  split <;> split <;> rfl
