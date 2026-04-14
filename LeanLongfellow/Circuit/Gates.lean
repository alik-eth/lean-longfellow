import LeanLongfellow.Circuit.Defs

open Finset MultilinearPoly

set_option autoImplicit false

/-! # Gate-level Circuit Representation Bridge

Maps concrete gate descriptions (add/mul with Boolean-vector indices)
to the abstract `CircuitLayer` model with multilinear indicator polynomials.
-/

-- ============================================================
-- Section 1: Gate types
-- ============================================================

/-- The two gate types in an arithmetic circuit. -/
inductive GateType where
  | add
  | mul
  deriving DecidableEq, BEq

/-- A gate in a layer with `2^s` positions, indexed by Boolean vectors of length `s`. -/
structure Gate (s : ℕ) where
  gateType : GateType
  output : Fin s → Bool
  left : Fin s → Bool
  right : Fin s → Bool

-- ============================================================
-- Section 2: Splitting a 3s-vector into (g, l, r)
-- ============================================================

/-- Extract the first s bits (gate index) from a 3s-vector. -/
def splitG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val, by omega⟩

/-- Extract the middle s bits (left input) from a 3s-vector. -/
def splitLG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val + s, by omega⟩

/-- Extract the last s bits (right input) from a 3s-vector. -/
def splitRG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val + 2 * s, by omega⟩

-- ============================================================
-- Section 3: Split/concat round-trip lemmas
-- ============================================================

@[simp] theorem splitG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitG (concat3 g l r) = g := by
  funext j
  simp [splitG, concat3, j.isLt]

@[simp] theorem splitLG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitLG (concat3 g l r) = l := by
  funext j
  simp only [splitLG, concat3]
  have h1 : ¬(j.val + s < s) := by omega
  have h2 : j.val + s < 2 * s := by omega
  simp [h1, h2, show j.val + s - s = j.val by omega]

@[simp] theorem splitRG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitRG (concat3 g l r) = r := by
  funext j
  simp only [splitRG, concat3]
  have h1 : ¬(j.val + 2 * s < s) := by omega
  have h2 : ¬(j.val + 2 * s < 2 * s) := by omega
  simp [h1, h2, show j.val + 2 * s - 2 * s = j.val by omega]

@[simp] theorem concat3_splitG_splitLG_splitRG {s : ℕ} (glr : Fin (3 * s) → Bool) :
    concat3 (splitG glr) (splitLG glr) (splitRG glr) = glr := by
  funext ⟨k, hk⟩
  simp only [concat3, splitG, splitLG, splitRG]
  split
  case isTrue h => rfl
  case isFalse h1 =>
    split
    case isTrue h2 =>
      have : (⟨k - s + s, by omega⟩ : Fin (3 * s)) = ⟨k, hk⟩ := by
        apply Fin.ext; simp; omega
      rw [this]
    case isFalse h2 =>
      have : (⟨k - 2 * s + 2 * s, by omega⟩ : Fin (3 * s)) = ⟨k, hk⟩ := by
        apply Fin.ext; simp; omega
      rw [this]

-- ============================================================
-- Section 4: Gate matching
-- ============================================================

/-- Does a gate match position (g, l, r) with the given type? -/
def Gate.matches {s : ℕ} (gate : Gate s) (ty : GateType) (g l r : Fin s → Bool) : Bool :=
  decide (gate.gateType = ty) && decide (gate.output = g) &&
  decide (gate.left = l) && decide (gate.right = r)

theorem Gate.matches_iff {s : ℕ} (gate : Gate s) (ty : GateType) (g l r : Fin s → Bool) :
    gate.matches ty g l r = true ↔
    gate.gateType = ty ∧ gate.output = g ∧ gate.left = l ∧ gate.right = r := by
  simp [Gate.matches, Bool.and_eq_true, decide_eq_true_eq]
  tauto

-- ============================================================
-- Section 5: Building a CircuitLayer from gates
-- ============================================================

/-- Build a `CircuitLayer` from a list of gates.
    `add_poly.table(g,l,r) = 1` if there is an add gate `(g,l,r)`, else `0`.
    `mul_poly.table(g,l,r) = 1` if there is a mul gate `(g,l,r)`, else `0`. -/
def gatesToLayer {s : ℕ} (F : Type*) [Field F] (gates : List (Gate s)) :
    CircuitLayer F s where
  add_poly := ⟨fun glr =>
    if gates.any (fun gate => gate.matches .add (splitG glr) (splitLG glr) (splitRG glr))
    then 1 else 0⟩
  mul_poly := ⟨fun glr =>
    if gates.any (fun gate => gate.matches .mul (splitG glr) (splitLG glr) (splitRG glr))
    then 1 else 0⟩

-- ============================================================
-- Section 6: Correctness theorem
-- ============================================================

/-- If each gate is correctly evaluated, each output position has at most one gate,
    and uncovered positions have value 0, then `layerConsistent` holds. -/
theorem gatesToLayer_consistent {s : ℕ} {F : Type*} [Field F]
    (gates : List (Gate s))
    (V_curr V_next : LayerValues F s)
    -- Each gate is correctly evaluated
    (heval : ∀ gate ∈ gates, match gate.gateType with
      | .add => V_curr.table gate.output =
                V_next.table gate.left + V_next.table gate.right
      | .mul => V_curr.table gate.output =
                V_next.table gate.left * V_next.table gate.right)
    -- Each output position has at most one gate
    (huniq : ∀ g : Fin s → Bool,
      (gates.filter (fun gate => decide (gate.output = g))).length ≤ 1)
    -- Uncovered output positions have value 0
    (hcovered : ∀ g : Fin s → Bool,
      (¬ gates.any (fun gate => decide (gate.output = g))) →
      V_curr.table g = 0)
    (g : Fin s → Bool) :
    layerConsistent (gatesToLayer F gates) V_curr V_next g := by
  sorry
