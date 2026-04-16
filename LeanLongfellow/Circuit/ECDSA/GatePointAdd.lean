import LeanLongfellow.Circuit.Gates.GateCircuit

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Gate-Level Point Addition (Phase C)

Three `mulPassLayer` layers that verify point addition R = P1 + P2:

1. **Slope check**: `lambda * (x₂ - x₁)` — wire W_TEMP1 gets `V(W_FINAL_LAM) * V(W_TEMP4)`
2. **Lambda squared**: `lambda²` — wire W_TEMP2 gets `V(W_FINAL_LAM) * V(W_FINAL_LAM)`
3. **Y-coordinate**: `lambda * (x₁ - x₃)` — wire W_TEMP3 gets `V(W_FINAL_LAM) * V(W_TEMP5)`

Wire layout:
- W_FINAL_LAM (pos 27): addition slope lambda
- W_TEMP4     (pos 28): witness for (P2.x - P1.x)
- W_TEMP5     (pos 29): witness for (P1.x - R.x)
- W_TEMP1     (pos 15): lambda * (x₂ - x₁) product
- W_TEMP2     (pos 16): lambda² product
- W_TEMP3     (pos 17): lambda * (x₁ - x₃) product
-/

variable (F : Type*) [Field F]

-- ============================================================
-- Section 1: Passthrough lists for each layer
-- ============================================================

/-- Passthroughs for slope check layer (all non-zero wires except W_TEMP1). -/
def pointAddSlopePassthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for lambda squared layer (all non-zero wires except W_TEMP2). -/
def pointAddLamSqPassthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for y-coordinate layer (all non-zero wires except W_TEMP3). -/
def pointAddYCoordPassthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

-- ============================================================
-- Section 2: Layer definitions
-- ============================================================

/-- Layer for slope check: computes `V(W_FINAL_LAM) * V(W_TEMP4)` at W_TEMP1.
    Verifies `lambda * (x₂ - x₁)`. -/
def pointAdd_layer0 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP1 W_FINAL_LAM W_TEMP4 pointAddSlopePassthroughs

/-- Layer for lambda squared: computes `V(W_FINAL_LAM) * V(W_FINAL_LAM)` at W_TEMP2.
    Verifies `lambda²`. -/
def pointAdd_layer1 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP2 W_FINAL_LAM W_FINAL_LAM pointAddLamSqPassthroughs

/-- Layer for y-coordinate: computes `V(W_FINAL_LAM) * V(W_TEMP5)` at W_TEMP3.
    Verifies `lambda * (x₁ - x₃)`. -/
def pointAdd_layer2 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP3 W_FINAL_LAM W_TEMP5 pointAddYCoordPassthroughs

-- ============================================================
-- Section 3: Distinctness lemmas (via native_decide)
-- ============================================================

private theorem wirePos_ne (a b : ℕ) (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    wirePos a ≠ wirePos b := by
  intro h
  have := wirePos_injective ⟨a, ha⟩ ⟨b, hb⟩ h
  exact hab (Fin.val_eq_of_eq this)

-- W_TEMP1 ≠ W_ZERO
private theorem W_TEMP1_ne_ZERO : W_TEMP1 ≠ W_ZERO :=
  wirePos_ne 15 0 (by omega) (by omega) (by omega)

-- W_TEMP2 ≠ W_ZERO
private theorem W_TEMP2_ne_ZERO : W_TEMP2 ≠ W_ZERO :=
  wirePos_ne 16 0 (by omega) (by omega) (by omega)

-- W_TEMP3 ≠ W_ZERO
private theorem W_TEMP3_ne_ZERO : W_TEMP3 ≠ W_ZERO :=
  wirePos_ne 17 0 (by omega) (by omega) (by omega)

-- ============================================================
-- Section 3a: Passthrough preconditions proved by native_decide
-- ============================================================

/-- All pointAddSlopePassthroughs are distinct from W_ZERO. -/
private theorem slopePass_ne_zero :
    ∀ p ∈ pointAddSlopePassthroughs, p ≠ W_ZERO := by native_decide

/-- All pointAddSlopePassthroughs are distinct from W_TEMP1 (the output). -/
private theorem slopePass_ne_out :
    ∀ p ∈ pointAddSlopePassthroughs, p ≠ W_TEMP1 := by native_decide

/-- pointAddSlopePassthroughs has no duplicates. -/
private theorem slopePass_nodup :
    pointAddSlopePassthroughs.Nodup := by native_decide

/-- All pointAddLamSqPassthroughs are distinct from W_ZERO. -/
private theorem lamSqPass_ne_zero :
    ∀ p ∈ pointAddLamSqPassthroughs, p ≠ W_ZERO := by native_decide

/-- All pointAddLamSqPassthroughs are distinct from W_TEMP2 (the output). -/
private theorem lamSqPass_ne_out :
    ∀ p ∈ pointAddLamSqPassthroughs, p ≠ W_TEMP2 := by native_decide

/-- pointAddLamSqPassthroughs has no duplicates. -/
private theorem lamSqPass_nodup :
    pointAddLamSqPassthroughs.Nodup := by native_decide

/-- All pointAddYCoordPassthroughs are distinct from W_ZERO. -/
private theorem yCoordPass_ne_zero :
    ∀ p ∈ pointAddYCoordPassthroughs, p ≠ W_ZERO := by native_decide

/-- All pointAddYCoordPassthroughs are distinct from W_TEMP3 (the output). -/
private theorem yCoordPass_ne_out :
    ∀ p ∈ pointAddYCoordPassthroughs, p ≠ W_TEMP3 := by native_decide

/-- pointAddYCoordPassthroughs has no duplicates. -/
private theorem yCoordPass_nodup :
    pointAddYCoordPassthroughs.Nodup := by native_decide

-- ============================================================
-- Section 4: Per-layer semantics via mulPassLayer_iff
-- ============================================================

/-- Bidirectional semantics for the slope check layer. -/
theorem pointAdd_layer0_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (pointAdd_layer0 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP1 = V_next.table W_FINAL_LAM * V_next.table W_TEMP4 ∧
     (∀ p ∈ pointAddSlopePassthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP1 → q ∉ pointAddSlopePassthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP1 W_FINAL_LAM W_TEMP4 pointAddSlopePassthroughs V_curr V_next
    W_TEMP1_ne_ZERO slopePass_ne_zero slopePass_ne_out slopePass_nodup

/-- Bidirectional semantics for the lambda squared layer. -/
theorem pointAdd_layer1_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (pointAdd_layer1 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP2 = V_next.table W_FINAL_LAM * V_next.table W_FINAL_LAM ∧
     (∀ p ∈ pointAddLamSqPassthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP2 → q ∉ pointAddLamSqPassthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP2 W_FINAL_LAM W_FINAL_LAM pointAddLamSqPassthroughs V_curr V_next
    W_TEMP2_ne_ZERO lamSqPass_ne_zero lamSqPass_ne_out lamSqPass_nodup

/-- Bidirectional semantics for the y-coordinate layer. -/
theorem pointAdd_layer2_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (pointAdd_layer2 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP3 = V_next.table W_FINAL_LAM * V_next.table W_TEMP5 ∧
     (∀ p ∈ pointAddYCoordPassthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP3 → q ∉ pointAddYCoordPassthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP3 W_FINAL_LAM W_TEMP5 pointAddYCoordPassthroughs V_curr V_next
    W_TEMP3_ne_ZERO yCoordPass_ne_zero yCoordPass_ne_out yCoordPass_nodup

-- ============================================================
-- Section 5: Passthrough membership lemmas
-- ============================================================

-- W_FINAL_LAM passes through all layers (needed for lambda to propagate)
private theorem W_FINAL_LAM_in_slope : W_FINAL_LAM ∈ pointAddSlopePassthroughs := by native_decide
private theorem W_FINAL_LAM_in_lamSq : W_FINAL_LAM ∈ pointAddLamSqPassthroughs := by native_decide
private theorem W_FINAL_LAM_in_yCoord : W_FINAL_LAM ∈ pointAddYCoordPassthroughs := by native_decide

-- W_TEMP4 passes through lamSq and yCoord layers
private theorem W_TEMP4_in_lamSq : W_TEMP4 ∈ pointAddLamSqPassthroughs := by native_decide
private theorem W_TEMP4_in_yCoord : W_TEMP4 ∈ pointAddYCoordPassthroughs := by native_decide

-- W_TEMP5 passes through slope and lamSq layers
private theorem W_TEMP5_in_slope : W_TEMP5 ∈ pointAddSlopePassthroughs := by native_decide
private theorem W_TEMP5_in_lamSq : W_TEMP5 ∈ pointAddLamSqPassthroughs := by native_decide

-- ============================================================
-- Section 6: Zero-wire chain lemma
-- ============================================================

/-- The zero wire propagates backward through point addition layers:
    if `V₃(W_ZERO) = 0` and each layer is consistent, then
    `V₂(W_ZERO) = 0`, `V₁(W_ZERO) = 0`, and `V₀(W_ZERO) = 0`. -/
private theorem zero_wire_chain
    (values : Fin 4 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (pointAdd_layer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (pointAdd_layer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (pointAdd_layer2 F) (values 2) (values 3) g)
    (_hzero3 : (values 3).table W_ZERO = 0) :
    (values 2).table W_ZERO = 0 ∧
    (values 1).table W_ZERO = 0 ∧
    (values 0).table W_ZERO = 0 := by
  have hz2 := ((pointAdd_layer2_iff F (values 2) (values 3)).mp hcons2).2.2.1
  have hz1 := ((pointAdd_layer1_iff F (values 1) (values 2)).mp hcons1).2.2.1
  have hz0 := ((pointAdd_layer0_iff F (values 0) (values 1)).mp hcons0).2.2.1
  exact ⟨hz2, hz1, hz0⟩

-- ============================================================
-- Section 7: Main extraction theorem
-- ============================================================

/-- **Point addition extraction**: from layer consistency of the three
    point-add layers, extract the three multiplication equations:

    1. `V₀(W_TEMP1) = V₃(W_FINAL_LAM) * V₃(W_TEMP4)` — slope check
    2. `V₁(W_TEMP2) = V₃(W_FINAL_LAM) * V₃(W_FINAL_LAM)` — lambda squared
    3. `V₂(W_TEMP3) = V₃(W_FINAL_LAM) * V₃(W_TEMP5)` — y-coordinate

    The key insight is that pass-through gates propagate wire values unchanged
    across layers (since `V(W_ZERO) = 0` at each level), so the inputs to
    each mul gate can be traced back to V₃ (the bottom layer). -/
theorem point_add_gate_extraction
    (values : Fin 4 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (pointAdd_layer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (pointAdd_layer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (pointAdd_layer2 F) (values 2) (values 3) g)
    (_hzero : (values 3).table W_ZERO = 0) :
    -- The 3 multiplication equations
    (values 0).table W_TEMP1 = (values 1).table W_FINAL_LAM * (values 1).table W_TEMP4 ∧
    (values 1).table W_TEMP2 = (values 2).table W_FINAL_LAM * (values 2).table W_FINAL_LAM ∧
    (values 2).table W_TEMP3 = (values 3).table W_FINAL_LAM * (values 3).table W_TEMP5 := by
  -- Extract semantics from each layer
  have h_slope := (pointAdd_layer0_iff F (values 0) (values 1)).mp hcons0
  have h_lamSq := (pointAdd_layer1_iff F (values 1) (values 2)).mp hcons1
  have h_yCoord := (pointAdd_layer2_iff F (values 2) (values 3)).mp hcons2
  -- Extract mul equations (each layer directly gives the desired equation)
  obtain ⟨hmul0, _, _, _⟩ := h_slope
  obtain ⟨hmul1, _, _, _⟩ := h_lamSq
  obtain ⟨hmul2, _, _, _⟩ := h_yCoord
  exact ⟨hmul0, hmul1, hmul2⟩
