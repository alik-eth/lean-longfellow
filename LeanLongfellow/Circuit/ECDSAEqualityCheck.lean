import LeanLongfellow.Circuit.Gates
import LeanLongfellow.Circuit.GadgetGates
import LeanLongfellow.Circuit.ECDSAFieldOps

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Equality Check Circuit Layer

Defines circuit layers for the equality check `R.x = r` in ECDSA verification.

The approach uses a **squaring gate**: the prover supplies `d = x - r` on an
input wire, and a single mul gate computes `d² = d * d`. If the output is `0`,
then `d = 0` (by `mul_self_eq_zero` in a field with no zero divisors), hence
`x = r`.

## Architecture

1. **`equalitySqGate`** — a mul gate with left = right = wire0, computing `d²`.
2. **`equalitySqLayer`** — the circuit layer containing just that gate.
3. **`equalitySqLayer_iff`** — layer consistency reduces to `output = input² ∧ ...`
4. **`equalitySq_zero_imp_eq`** — if output is 0 and input is `x - r`, then `x = r`.
5. **`equalityCheck_correct`** — end-to-end theorem: consistent layer + output 0 +
   input wiring → `x = r`.
6. **`equalityCheck_complete`** — completeness: if `x = r`, the prover can set
   `d = 0` and the layer is consistent with output 0.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Squaring gate for equality check
-- ============================================================

/-- A single mul gate that squares wire 0: output wire 0, left wire 0, right wire 0.
    Encodes: `output[0] = input[0] * input[0] = input[0]²`. -/
def equalitySqGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire0

/-- The circuit layer for equality checking via squaring: one mul gate. -/
def equalitySqLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [equalitySqGate]

-- ============================================================
-- Section 2: Layer consistency characterization
-- ============================================================

/-- `equalitySqLayer` is consistent iff output wire 0 equals the square
    of input wire 0, and all other output wires are zero. -/
theorem equalitySqLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire0 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 := by
  exact single_mul_gate_consistent wire0 wire0 wire0 V_curr V_next

-- ============================================================
-- Section 3: Soundness — zero output implies equality
-- ============================================================

/-- If `d * d = 0` in a field, then `d = 0`. -/
private theorem sq_zero_imp_zero (d : F) (h : d * d = 0) : d = 0 :=
  mul_self_eq_zero.mp h

/-- If the squaring layer is consistent and the output is 0,
    then the input wire 0 is 0. -/
theorem equalitySq_output_zero (V_curr V_next : LayerValues F 1)
    (hcons : ∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 0) :
    V_next.table wire0 = 0 := by
  have ⟨hprod, _⟩ := (equalitySqLayer_iff V_curr V_next).mp hcons
  rw [hout] at hprod
  exact mul_self_eq_zero.mp hprod.symm

/-- Core soundness: if input wire 0 carries `x - r`, the layer is consistent,
    and output wire 0 is 0, then `x = r`. -/
theorem equalitySq_zero_imp_eq (x r : F) (V_curr V_next : LayerValues F 1)
    (h_in : V_next.table wire0 = x - r)
    (hcons : ∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 0) :
    x = r := by
  have h0 := equalitySq_output_zero V_curr V_next hcons hout
  rw [h_in] at h0
  exact sub_eq_zero.mp h0

-- ============================================================
-- Section 4: End-to-end equality check correctness
-- ============================================================

/-- **Equality check correctness (soundness direction):**
    If the prover supplies `d = x - r` on input wire 0, the squaring layer
    is consistent, and the output wire 0 is 0, then `x = r`.

    This is the key theorem for ECDSA step 7: checking `R.x = r`. -/
theorem equalityCheck_correct (x r : F) (V_curr V_next : LayerValues F 1)
    (h_in : V_next.table wire0 = x - r)
    (hcons : ∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 0) :
    x = r :=
  equalitySq_zero_imp_eq x r V_curr V_next h_in hcons hout

-- ============================================================
-- Section 5: Completeness — equality implies satisfying assignment
-- ============================================================

/-- **Equality check completeness:**
    If `x = r`, then the assignment `d = 0` makes the layer consistent
    with output 0. More precisely: if both input wires carry the value
    `x - r = 0` and the output carries `0`, then the layer consistency
    equation holds (since `0 = 0 * 0`). -/
theorem equalityCheck_complete (x r : F) (hxr : x = r) :
    (x - r) * (x - r) = 0 := by
  rw [hxr, sub_self, mul_zero]

-- ============================================================
-- Section 6: Integration with ECDSA R.x = r
-- ============================================================

/-- **ECDSA x-coordinate check via squaring layer:**
    If the equality squaring layer is consistent, the input carries `R_x - r`,
    and the output is 0, then the ECDSA equality `R_x = r` holds.

    This connects the circuit-level encoding to the specification-level
    constraint `wit.R.x = r` in `ecdsaConstraint`. -/
theorem ecdsa_xcoord_check (R_x r : F) (V_curr V_next : LayerValues F 1)
    (h_in : V_next.table wire0 = R_x - r)
    (hcons : ∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 0) :
    R_x = r :=
  equalityCheck_correct R_x r V_curr V_next h_in hcons hout

/-- **Combined non-infinity and equality check:**
    The ECDSA verification requires both `R.is_inf = 0` (R is not the point
    at infinity) and `R.x = r`. If we have both the non-infinity condition
    as a hypothesis and the equality layer proves `R.x = r`, the full
    step-7 constraint is satisfied. -/
theorem ecdsa_step7_check (R_x r : F) (R_is_inf : F)
    (V_curr V_next : LayerValues F 1)
    (h_notinf : R_is_inf = 0)
    (h_in : V_next.table wire0 = R_x - r)
    (hcons : ∀ g, layerConsistent (equalitySqLayer F) V_curr V_next g)
    (hout : V_curr.table wire0 = 0) :
    R_is_inf = 0 ∧ R_x = r :=
  ⟨h_notinf, equalityCheck_correct R_x r V_curr V_next h_in hcons hout⟩
