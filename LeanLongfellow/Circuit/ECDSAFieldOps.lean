import LeanLongfellow.Circuit.Gates
import LeanLongfellow.Circuit.GadgetGates

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Field Operations as Circuit Layers

Defines single-gate circuit layers for two ECDSA sub-operations:

1. **Inverse check**: verify `s * s_inv = 1` via a mul gate.
2. **Field multiplication**: compute `u = z * s_inv` via a mul gate.

Both are 1-gate circuits with `s = 1` (2 wires per layer: wire 0 and wire 1).
Correctness is proved by reducing to `single_mul_gate_consistent`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Wire naming helpers for s = 1
-- ============================================================

/-- Wire 0: the all-false Boolean vector of length 1. -/
abbrev wire0 : Fin 1 → Bool := fun _ => false

/-- Wire 1: the all-true Boolean vector of length 1. -/
abbrev wire1 : Fin 1 → Bool := fun _ => true

/-- Every `Fin 1 → Bool` is either `wire0` or `wire1`. -/
private theorem wire_dichotomy (f : Fin 1 → Bool) : f = wire0 ∨ f = wire1 := by
  rcases hf : f 0 with _ | _
  · left; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf
  · right; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf

-- ============================================================
-- Section 2: Inverse check layer
-- ============================================================

/-- A single mul gate: output wire 0, left wire 0, right wire 1.
    Encodes: `output[0] = input[0] * input[1]`. -/
def inverseCheckGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire1

/-- The circuit layer for inverse verification: one mul gate. -/
def inverseCheckLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [inverseCheckGate]

/-- `inverseCheckLayer` is consistent iff wire 0 of the output equals
    the product of input wire 0 and input wire 1, and wire 1 of the
    output is zero. -/
theorem inverseCheckLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (inverseCheckLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire1 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 := by
  exact single_mul_gate_consistent wire0 wire0 wire1 V_curr V_next

/-- If the inverse check layer is consistent and output wire 0 equals 1,
    then `input[0] * input[1] = 1`, i.e., input[1] is the field inverse
    of input[0]. -/
theorem inverseCheck_correct (V_curr V_next : LayerValues F 1)
    (hcons : ∀ g, layerConsistent (inverseCheckLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 1) :
    V_next.table wire0 * V_next.table wire1 = 1 := by
  have ⟨hprod, _⟩ := (inverseCheckLayer_iff V_curr V_next).mp hcons
  rw [← hprod]; exact hout

/-- If wire 0 of the input is `s`, wire 1 is `s_inv`, and the
    output wire 0 is 1, then `s * s_inv = 1`. -/
theorem inverseCheck_spec (s_val s_inv : F) (V_curr V_next : LayerValues F 1)
    (hs : V_next.table wire0 = s_val)
    (hsinv : V_next.table wire1 = s_inv)
    (hcons : ∀ g, layerConsistent (inverseCheckLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 1) :
    s_val * s_inv = 1 := by
  have := inverseCheck_correct V_curr V_next hcons hout
  rw [hs, hsinv] at this
  exact this

-- ============================================================
-- Section 3: Field multiplication layer
-- ============================================================

/-- A single mul gate for field multiplication: output wire 0, left wire 0, right wire 1.
    Encodes: `output[0] = input[0] * input[1]`.
    (Same gate structure as inverseCheckGate, reused for multiplication.) -/
def fieldMulGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire1

/-- The circuit layer for field multiplication: one mul gate. -/
def fieldMulLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [fieldMulGate]

/-- `fieldMulLayer` is consistent iff output wire 0 equals
    the product of input wire 0 and input wire 1, and wire 1 output is zero. -/
theorem fieldMulLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (fieldMulLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire1 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 := by
  exact single_mul_gate_consistent wire0 wire0 wire1 V_curr V_next

/-- If the multiplication layer is consistent and the inputs are `z` and `s_inv`,
    then output wire 0 equals `z * s_inv`. -/
theorem fieldMul_correct (z s_inv : F) (V_curr V_next : LayerValues F 1)
    (hz : V_next.table wire0 = z)
    (hsinv : V_next.table wire1 = s_inv)
    (hcons : ∀ g, layerConsistent (fieldMulLayer F) V_curr V_next g) :
    V_curr.table wire0 = z * s_inv := by
  have ⟨hprod, _⟩ := (fieldMulLayer_iff V_curr V_next).mp hcons
  rw [hprod, hz, hsinv]

-- ============================================================
-- Section 4: Combined specification for ECDSA u-computation
-- ============================================================

/-- End-to-end specification: if we have an inverse check layer followed by a
    multiplication layer (sharing the `s_inv` wire), the composed result
    computes `u = z * s⁻¹` given `s * s_inv = 1`.

    This captures the ECDSA sub-computation `u₁ = z * s⁻¹ mod n`. -/
theorem ecdsa_u_computation
    (s_val z s_inv u : F)
    -- Inverse check layer
    (V_inv_out V_inv_in : LayerValues F 1)
    (hs_inv_in0 : V_inv_in.table wire0 = s_val)
    (hs_inv_in1 : V_inv_in.table wire1 = s_inv)
    (hcons_inv : ∀ g, layerConsistent (inverseCheckLayer F) V_inv_out V_inv_in g)
    (hout_inv : V_inv_out.table wire0 = 1)
    -- Multiplication layer
    (V_mul_out V_mul_in : LayerValues F 1)
    (hz_in : V_mul_in.table wire0 = z)
    (hsinv_in : V_mul_in.table wire1 = s_inv)
    (hcons_mul : ∀ g, layerConsistent (fieldMulLayer F) V_mul_out V_mul_in g)
    (hu_out : V_mul_out.table wire0 = u) :
    s_val * s_inv = 1 ∧ u = z * s_inv := by
  constructor
  · exact inverseCheck_spec s_val s_inv V_inv_out V_inv_in hs_inv_in0 hs_inv_in1 hcons_inv hout_inv
  · rw [← hu_out]
    exact fieldMul_correct z s_inv V_mul_out V_mul_in hz_in hsinv_in hcons_mul
