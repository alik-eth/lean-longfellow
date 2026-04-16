import LeanLongfellow.Circuit.Core.Defs
import LeanLongfellow.Circuit.Core.EqPoly

open Finset MultilinearPoly

variable {F : Type*} [Field F] {s : ℕ}

/-! # Combining Polynomial

The GKR/Longfellow combining polynomial for a single-layer reduction:
`Q(l, r) = ∑_g eq(t, g) · [add(g,l,r)·(V(l) + V(r)) + mul(g,l,r)·V(l)·V(r)]`
-/

-- ============================================================
-- Section 1: Helper lemmas for boolToField / split interaction
-- ============================================================

/-- `splitL` commutes with `boolToField`. -/
theorem splitL_boolToField (lr : Fin (2 * s) → Bool) :
    splitL (boolToField (F := F) lr) = boolToField (splitL lr) := by
  funext j
  simp [splitL, boolToField]

/-- `splitR` commutes with `boolToField`. -/
theorem splitR_boolToField (lr : Fin (2 * s) → Bool) :
    splitR (boolToField (F := F) lr) = boolToField (splitR lr) := by
  funext j
  simp [splitR, boolToField]

-- ============================================================
-- Section 2: Combining polynomial definition
-- ============================================================

/-- The combining polynomial Q(l,r) for a single GKR layer reduction.
    Given a fixed challenge point `t ∈ F^s` and the next layer's values V_next,
    Q(l, r) = ∑_g eq(t, g) · [add(g,l,r)·(V(l) + V(r)) + mul(g,l,r)·V(l)·V(r)] -/
noncomputable def combiningPoly (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    (Fin (2 * s) → F) → F :=
  fun lr =>
    let l := splitL lr
    let r := splitR lr
    ∑ g : Fin s → Bool,
      eqPoly t (boolToField g) *
      (layer.add_poly.eval (concat3 (boolToField g) l r) *
        (V_next.eval l + V_next.eval r) +
       layer.mul_poly.eval (concat3 (boolToField g) l r) *
        (V_next.eval l * V_next.eval r))

/-- The combining polynomial packaged as a multilinear polynomial over 2s variables. -/
noncomputable def combiningPolyMLE (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    MultilinearPoly F (2 * s) where
  table := fun b => combiningPoly layer t V_next (boolToField b)

-- ============================================================
-- Section 3: Main correctness theorem
-- ============================================================

/-- Summing the combining polynomial over the Boolean hypercube recovers V_curr(t).
    This is the core identity that makes the GKR sumcheck reduction work. -/
theorem combiningPoly_sum (layer : CircuitLayer F s)
    (t : Fin s → Bool) (V_curr V_next : LayerValues F s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g) :
    ∑ lr : Fin (2 * s) → Bool,
      combiningPoly layer (boolToField t) V_next (boolToField lr) =
    V_curr.table t := by
  -- Step 1: Unfold combiningPoly
  simp only [combiningPoly]
  -- Step 2: Swap sums: ∑_lr ∑_g → ∑_g ∑_lr
  rw [Finset.sum_comm]
  -- Step 3: Factor out eqPoly(t,g) from inner sum
  conv_lhs =>
    arg 2; ext g
    rw [← Finset.mul_sum]
  -- Step 4: Simplify eval on Boolean inputs
  conv_lhs =>
    arg 2; ext g; arg 2; arg 2; ext lr
    rw [splitL_boolToField, splitR_boolToField]
    rw [eval_boolVec, eval_boolVec]
    rw [concat3_boolToField]
    rw [eval_boolVec, eval_boolVec]
  -- Step 5: The inner sum now matches layerConsistent
  -- Rewrite using hcons
  conv_lhs =>
    arg 2; ext g
    rw [show (∑ lr : Fin (2 * s) → Bool,
        (layer.add_poly.table (concat3 g (splitL lr) (splitR lr)) *
          (V_next.table (splitL lr) + V_next.table (splitR lr)) +
         layer.mul_poly.table (concat3 g (splitL lr) (splitR lr)) *
          (V_next.table (splitL lr) * V_next.table (splitR lr)))) =
        V_curr.table g from by rw [← hcons g]]
  -- Step 6: Apply eqPoly_select
  exact eqPoly_select t (fun g => V_curr.table g)

/-- Generalized sum theorem: works for any target `t ∈ F^s`, not just Boolean.
    The sum equals `V_curr.eval t` (MLE evaluation) instead of `V_curr.table t`. -/
theorem combiningPoly_sum_general (layer : CircuitLayer F s)
    (t : Fin s → F) (V_curr V_next : LayerValues F s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g) :
    ∑ lr : Fin (2 * s) → Bool,
      combiningPoly layer t V_next (boolToField lr) =
    V_curr.eval t := by
  -- Step 1: Unfold combiningPoly
  simp only [combiningPoly]
  -- Step 2: Swap sums: ∑_lr ∑_g → ∑_g ∑_lr
  rw [Finset.sum_comm]
  -- Step 3: Factor out eqPoly(t,g) from inner sum
  conv_lhs =>
    arg 2; ext g
    rw [← Finset.mul_sum]
  -- Step 4: Simplify eval on Boolean inputs
  conv_lhs =>
    arg 2; ext g; arg 2; arg 2; ext lr
    rw [splitL_boolToField, splitR_boolToField]
    rw [eval_boolVec, eval_boolVec]
    rw [concat3_boolToField]
    rw [eval_boolVec, eval_boolVec]
  -- Step 5: The inner sum now matches layerConsistent
  conv_lhs =>
    arg 2; ext g
    rw [show (∑ lr : Fin (2 * s) → Bool,
        (layer.add_poly.table (concat3 g (splitL lr) (splitR lr)) *
          (V_next.table (splitL lr) + V_next.table (splitR lr)) +
         layer.mul_poly.table (concat3 g (splitL lr) (splitR lr)) *
          (V_next.table (splitL lr) * V_next.table (splitR lr)))) =
        V_curr.table g from by rw [← hcons g]]
  -- Step 6: Apply eqPoly_eval to get V_curr.eval t
  exact eqPoly_eval t V_curr
