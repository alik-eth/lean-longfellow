import LeanLongfellow.Circuit.GateCircuit

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Gate-Level Field Operations (Phase A)

Three `mulPassLayer` layers that verify the ECDSA field operations:

1. **Inverse check**: `s * s_inv` — wire W_TEMP1 gets `V(W_TEMP4) * V(W_SINV)`
2. **u1 computation**: `z * s_inv` — wire W_U1 gets `V(W_TEMP5) * V(W_SINV)`
3. **u2 computation**: `r * s_inv` — wire W_U2 gets `V(W_ZCHECK) * V(W_SINV)`

Wire layout in V_NL (the bottom layer values):
- W_SINV  (pos 1):  s_inv
- W_U1    (pos 2):  u1 (overwritten by layer 2)
- W_U2    (pos 3):  u2 (overwritten by layer 3)
- W_TEMP1 (pos 15): s * s_inv product (overwritten by layer 1)
- W_TEMP4 (pos 28): s (signature component)
- W_TEMP5 (pos 29): z (message hash)
- W_ZCHECK(pos 30): r (signature r component)
-/

variable (F : Type*) [Field F]

-- ============================================================
-- Section 1: Passthrough lists for each layer
-- ============================================================

/-- All 30 non-zero wire positions (positions 1–31), used as a base for passthroughs. -/
private def allNonZeroWires : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for the inverse check layer (all non-zero wires except W_TEMP1). -/
def invCheckPassthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for the u1 computation layer (all non-zero wires except W_U1). -/
def u1Passthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for the u2 computation layer (all non-zero wires except W_U2). -/
def u2Passthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

-- ============================================================
-- Section 2: Layer definitions
-- ============================================================

/-- Layer for inverse check: computes `V(W_TEMP4) * V(W_SINV)` at W_TEMP1.
    Verifies `s * s_inv`. -/
def fieldOps_invCheck : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP1 W_TEMP4 W_SINV invCheckPassthroughs

/-- Layer for u1 computation: computes `V(W_TEMP5) * V(W_SINV)` at W_U1.
    Verifies `u1 = z * s_inv`. -/
def fieldOps_u1 : CircuitLayer F 5 :=
  mulPassLayer F W_U1 W_TEMP5 W_SINV u1Passthroughs

/-- Layer for u2 computation: computes `V(W_ZCHECK) * V(W_SINV)` at W_U2.
    Verifies `u2 = r * s_inv`. -/
def fieldOps_u2 : CircuitLayer F 5 :=
  mulPassLayer F W_U2 W_ZCHECK W_SINV u2Passthroughs

-- ============================================================
-- Section 3: Distinctness lemmas (via native_decide)
-- ============================================================

-- Helper to convert wire position inequality to Fin 32 inequality
private theorem wirePos_ne (a b : ℕ) (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    wirePos a ≠ wirePos b := by
  intro h
  have := wirePos_injective ⟨a, ha⟩ ⟨b, hb⟩ h
  exact hab (Fin.val_eq_of_eq this)

-- W_TEMP1 ≠ W_ZERO
private theorem W_TEMP1_ne_ZERO : W_TEMP1 ≠ W_ZERO :=
  wirePos_ne 15 0 (by omega) (by omega) (by omega)

-- W_U1 ≠ W_ZERO
private theorem W_U1_ne_ZERO : W_U1 ≠ W_ZERO :=
  wirePos_ne 2 0 (by omega) (by omega) (by omega)

-- W_U2 ≠ W_ZERO
private theorem W_U2_ne_ZERO : W_U2 ≠ W_ZERO :=
  wirePos_ne 3 0 (by omega) (by omega) (by omega)

-- ============================================================
-- Section 3a: Passthrough preconditions proved by native_decide
-- ============================================================

/-- All invCheckPassthroughs are distinct from W_ZERO. -/
private theorem invCheckPass_ne_zero :
    ∀ p ∈ invCheckPassthroughs, p ≠ W_ZERO := by native_decide

/-- All invCheckPassthroughs are distinct from W_TEMP1 (the output). -/
private theorem invCheckPass_ne_out :
    ∀ p ∈ invCheckPassthroughs, p ≠ W_TEMP1 := by native_decide

/-- invCheckPassthroughs has no duplicates. -/
private theorem invCheckPass_nodup :
    invCheckPassthroughs.Nodup := by native_decide

/-- All u1Passthroughs are distinct from W_ZERO. -/
private theorem u1Pass_ne_zero :
    ∀ p ∈ u1Passthroughs, p ≠ W_ZERO := by native_decide

/-- All u1Passthroughs are distinct from W_U1 (the output). -/
private theorem u1Pass_ne_out :
    ∀ p ∈ u1Passthroughs, p ≠ W_U1 := by native_decide

/-- u1Passthroughs has no duplicates. -/
private theorem u1Pass_nodup :
    u1Passthroughs.Nodup := by native_decide

/-- All u2Passthroughs are distinct from W_ZERO. -/
private theorem u2Pass_ne_zero :
    ∀ p ∈ u2Passthroughs, p ≠ W_ZERO := by native_decide

/-- All u2Passthroughs are distinct from W_U2 (the output). -/
private theorem u2Pass_ne_out :
    ∀ p ∈ u2Passthroughs, p ≠ W_U2 := by native_decide

/-- u2Passthroughs has no duplicates. -/
private theorem u2Pass_nodup :
    u2Passthroughs.Nodup := by native_decide

-- ============================================================
-- Section 4: Per-layer semantics via mulPassLayer_iff
-- ============================================================

/-- Bidirectional semantics for the inverse check layer. -/
theorem fieldOps_invCheck_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (fieldOps_invCheck F) V_curr V_next g) ↔
    (V_curr.table W_TEMP1 = V_next.table W_TEMP4 * V_next.table W_SINV ∧
     (∀ p ∈ invCheckPassthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP1 → q ∉ invCheckPassthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP1 W_TEMP4 W_SINV invCheckPassthroughs V_curr V_next
    W_TEMP1_ne_ZERO invCheckPass_ne_zero invCheckPass_ne_out invCheckPass_nodup

/-- Bidirectional semantics for the u1 computation layer. -/
theorem fieldOps_u1_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (fieldOps_u1 F) V_curr V_next g) ↔
    (V_curr.table W_U1 = V_next.table W_TEMP5 * V_next.table W_SINV ∧
     (∀ p ∈ u1Passthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_U1 → q ∉ u1Passthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_U1 W_TEMP5 W_SINV u1Passthroughs V_curr V_next
    W_U1_ne_ZERO u1Pass_ne_zero u1Pass_ne_out u1Pass_nodup

/-- Bidirectional semantics for the u2 computation layer. -/
theorem fieldOps_u2_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (fieldOps_u2 F) V_curr V_next g) ↔
    (V_curr.table W_U2 = V_next.table W_ZCHECK * V_next.table W_SINV ∧
     (∀ p ∈ u2Passthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_U2 → q ∉ u2Passthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_U2 W_ZCHECK W_SINV u2Passthroughs V_curr V_next
    W_U2_ne_ZERO u2Pass_ne_zero u2Pass_ne_out u2Pass_nodup

-- ============================================================
-- Section 5: Passthrough membership lemmas
-- ============================================================

-- W_SINV is in all passthrough lists
private theorem W_SINV_in_invCheck : W_SINV ∈ invCheckPassthroughs := by native_decide
private theorem W_SINV_in_u1 : W_SINV ∈ u1Passthroughs := by native_decide
private theorem W_SINV_in_u2 : W_SINV ∈ u2Passthroughs := by native_decide

-- W_TEMP4 passes through u1 and u2 layers (needed for s to propagate)
private theorem W_TEMP4_in_u1 : W_TEMP4 ∈ u1Passthroughs := by native_decide
private theorem W_TEMP4_in_u2 : W_TEMP4 ∈ u2Passthroughs := by native_decide

-- W_TEMP5 passes through u2 layer (needed for z to propagate)
private theorem W_TEMP5_in_invCheck : W_TEMP5 ∈ invCheckPassthroughs := by native_decide
private theorem W_TEMP5_in_u2 : W_TEMP5 ∈ u2Passthroughs := by native_decide

-- W_ZCHECK passes through invCheck and u1 layers (needed for r to propagate)
private theorem W_ZCHECK_in_invCheck : W_ZCHECK ∈ invCheckPassthroughs := by native_decide
private theorem W_ZCHECK_in_u1 : W_ZCHECK ∈ u1Passthroughs := by native_decide

-- ============================================================
-- Section 6: Zero-wire chain lemma
-- ============================================================

/-- The zero wire propagates backward through field ops layers:
    if `V₃(W_ZERO) = 0` and each layer is consistent, then
    `V₂(W_ZERO) = 0`, `V₁(W_ZERO) = 0`, and `V₀(W_ZERO) = 0`. -/
private theorem zero_wire_chain
    (values : Fin 4 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (fieldOps_invCheck F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (fieldOps_u1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (fieldOps_u2 F) (values 2) (values 3) g)
    (_hzero3 : (values 3).table W_ZERO = 0) :
    (values 2).table W_ZERO = 0 ∧
    (values 1).table W_ZERO = 0 ∧
    (values 0).table W_ZERO = 0 := by
  have hz2 := ((fieldOps_u2_iff F (values 2) (values 3)).mp hcons2).2.2.1
  have hz1 := ((fieldOps_u1_iff F (values 1) (values 2)).mp hcons1).2.2.1
  have hz0 := ((fieldOps_invCheck_iff F (values 0) (values 1)).mp hcons0).2.2.1
  exact ⟨hz2, hz1, hz0⟩

-- ============================================================
-- Section 7: Main extraction theorem
-- ============================================================

/-- **Field operations extraction**: from layer consistency of the three
    field-ops layers, extract the three multiplication equations:

    1. `V₀(W_TEMP1) = V₃(W_TEMP4) * V₃(W_SINV)` — the `s * s_inv` product
    2. `V₁(W_U1) = V₃(W_TEMP5) * V₃(W_SINV)` — the `u1 = z * s_inv` equation
    3. `V₂(W_U2) = V₃(W_ZCHECK) * V₃(W_SINV)` — the `u2 = r * s_inv` equation

    The key insight is that pass-through gates propagate wire values unchanged
    across layers (since `V(W_ZERO) = 0` at each level), so the inputs to
    each mul gate can be traced back to V₃ (the bottom layer). -/
theorem field_ops_extraction
    (values : Fin 4 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (fieldOps_invCheck F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (fieldOps_u1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (fieldOps_u2 F) (values 2) (values 3) g)
    (hzero : (values 3).table W_ZERO = 0) :
    -- Equations extracted from layer consistency
    (values 0).table W_TEMP1 = (values 3).table W_TEMP4 * (values 3).table W_SINV ∧
    (values 1).table W_U1 = (values 3).table W_TEMP5 * (values 3).table W_SINV ∧
    (values 2).table W_U2 = (values 3).table W_ZCHECK * (values 3).table W_SINV := by
  -- Extract semantics from each layer
  have h_inv := (fieldOps_invCheck_iff F (values 0) (values 1)).mp hcons0
  have h_u1 := (fieldOps_u1_iff F (values 1) (values 2)).mp hcons1
  have h_u2 := (fieldOps_u2_iff F (values 2) (values 3)).mp hcons2
  -- Extract zero-wire facts
  have ⟨hz2, hz1, _⟩ := zero_wire_chain F values hcons0 hcons1 hcons2 hzero
  -- Extract mul equations
  obtain ⟨hmul0, hpass0, _, _⟩ := h_inv
  obtain ⟨hmul1, hpass1, _, _⟩ := h_u1
  obtain ⟨hmul2, hpass2, _, _⟩ := h_u2
  -- Trace W_SINV back through layers: V₁(W_SINV) = V₂(W_SINV) = V₃(W_SINV)
  have hsinv_12 : (values 1).table W_SINV = (values 2).table W_SINV :=
    passthrough_exact (hpass1 W_SINV W_SINV_in_u1) hz2
  have hsinv_23 : (values 2).table W_SINV = (values 3).table W_SINV :=
    passthrough_exact (hpass2 W_SINV W_SINV_in_u2) hzero
  -- Trace W_TEMP4 back: V₁(W_TEMP4) = V₂(W_TEMP4) = V₃(W_TEMP4)
  have htemp4_12 : (values 1).table W_TEMP4 = (values 2).table W_TEMP4 :=
    passthrough_exact (hpass1 W_TEMP4 W_TEMP4_in_u1) hz2
  have htemp4_23 : (values 2).table W_TEMP4 = (values 3).table W_TEMP4 :=
    passthrough_exact (hpass2 W_TEMP4 W_TEMP4_in_u2) hzero
  -- Trace W_TEMP5 back: V₂(W_TEMP5) = V₃(W_TEMP5)
  have htemp5_23 : (values 2).table W_TEMP5 = (values 3).table W_TEMP5 :=
    passthrough_exact (hpass2 W_TEMP5 W_TEMP5_in_u2) hzero
  -- Assemble the three equations
  refine ⟨?_, ?_, ?_⟩
  · -- s * s_inv equation: V₀(W_TEMP1) = V₃(W_TEMP4) * V₃(W_SINV)
    rw [hmul0, htemp4_12, htemp4_23, hsinv_12, hsinv_23]
  · -- u1 equation: V₁(W_U1) = V₃(W_TEMP5) * V₃(W_SINV)
    rw [hmul1, htemp5_23, hsinv_23]
  · -- u2 equation: V₂(W_U2) = V₃(W_ZCHECK) * V₃(W_SINV)
    rw [hmul2]
