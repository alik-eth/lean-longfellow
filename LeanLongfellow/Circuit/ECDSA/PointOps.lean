import LeanLongfellow.Circuit.ECArith
import LeanLongfellow.Circuit.GadgetGates
import LeanLongfellow.Circuit.ECDSAFieldOps

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Point Addition Circuit Layers

Defines single-gate circuit layers for the three multiplications in
elliptic curve point addition, then proves that layer consistency
implies the `ecAddConstraint` predicate from `ECArith.lean`.

Point addition (general case, `x₁ ≠ x₂`) requires three field
multiplications:
1. **Slope verification**: `lambda * (x₂ - x₁) = y₂ - y₁`
2. **Lambda squared**: `lambda² = lambda * lambda`
3. **Y computation**: `lambda * (x₁ - x₃)`

Each multiplication is encoded as a single mul gate in a layer with
`s = 1` (2 wires), reusing the `wire0`/`wire1` naming from
`ECDSAFieldOps.lean`.

Section 5 proves x-coordinate extraction: given `ecAddFull`, the
x-coordinate of the result is simply `R.x`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Slope verification layer
-- ============================================================

/-- Mul gate for slope verification: output wire 0, left wire 0, right wire 1.
    Encodes `output[0] = input[0] * input[1]`, i.e.,
    `lambda * diff_x` where `diff_x = x₂ - x₁`. -/
def slopeVerifyGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire1

/-- Circuit layer for slope verification: one mul gate. -/
def slopeVerifyLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [slopeVerifyGate]

/-- `slopeVerifyLayer` is consistent iff output wire 0 equals
    the product of input wire 0 and input wire 1, and wire 1 output
    is zero. -/
theorem slopeVerifyLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (slopeVerifyLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire1 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 :=
  single_mul_gate_consistent wire0 wire0 wire1 V_curr V_next

/-- If the slope verification layer is consistent with `lambda` on
    wire 0, `x₂ - x₁` on wire 1, and output wire 0 equals `y₂ - y₁`,
    then `lambda * (x₂ - x₁) = y₂ - y₁`. -/
theorem slopeVerify_correct (lambda diff_x diff_y : F)
    (V_curr V_next : LayerValues F 1)
    (h_in0 : V_next.table wire0 = lambda)
    (h_in1 : V_next.table wire1 = diff_x)
    (hcons : ∀ g, layerConsistent (slopeVerifyLayer F) V_curr V_next g)
    (h_out : V_curr.table wire0 = diff_y) :
    lambda * diff_x = diff_y := by
  have ⟨hprod, _⟩ := (slopeVerifyLayer_iff V_curr V_next).mp hcons
  rw [← h_out, hprod, h_in0, h_in1]

-- ============================================================
-- Section 2: Lambda-squared layer
-- ============================================================

/-- Mul gate for computing `lambda²`: output wire 0, left wire 0, right wire 1.
    Encodes `output[0] = input[0] * input[1]`, where both inputs carry `lambda`. -/
def lambdaSquaredGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire1

/-- Circuit layer for lambda squared: one mul gate. -/
def lambdaSquaredLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [lambdaSquaredGate]

/-- `lambdaSquaredLayer` is consistent iff output wire 0 equals
    the product of input wire 0 and input wire 1, and wire 1 output
    is zero. -/
theorem lambdaSquaredLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (lambdaSquaredLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire1 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 :=
  single_mul_gate_consistent wire0 wire0 wire1 V_curr V_next

/-- If the lambda-squared layer is consistent with `lambda` on both
    input wires, then output wire 0 equals `lambda * lambda`. -/
theorem lambdaSquared_correct (lambda : F)
    (V_curr V_next : LayerValues F 1)
    (h_in0 : V_next.table wire0 = lambda)
    (h_in1 : V_next.table wire1 = lambda)
    (hcons : ∀ g, layerConsistent (lambdaSquaredLayer F) V_curr V_next g) :
    V_curr.table wire0 = lambda * lambda := by
  have ⟨hprod, _⟩ := (lambdaSquaredLayer_iff V_curr V_next).mp hcons
  rw [hprod, h_in0, h_in1]

-- ============================================================
-- Section 3: Y-computation layer
-- ============================================================

/-- Mul gate for y-coordinate computation: output wire 0, left wire 0,
    right wire 1. Encodes `output[0] = input[0] * input[1]`, i.e.,
    `lambda * (x₁ - x₃)`. -/
def yComputeGate : Gate 1 where
  gateType := .mul
  output := wire0
  left := wire0
  right := wire1

/-- Circuit layer for y computation: one mul gate. -/
def yComputeLayer (F : Type*) [Field F] : CircuitLayer F 1 :=
  gatesToLayer F [yComputeGate]

/-- `yComputeLayer` is consistent iff output wire 0 equals
    the product of input wire 0 and input wire 1, and wire 1 output
    is zero. -/
theorem yComputeLayer_iff (V_curr V_next : LayerValues F 1) :
    (∀ g, layerConsistent (yComputeLayer F) V_curr V_next g) ↔
    V_curr.table wire0 = V_next.table wire0 * V_next.table wire1 ∧
    ∀ g', g' ≠ wire0 → V_curr.table g' = 0 :=
  single_mul_gate_consistent wire0 wire0 wire1 V_curr V_next

/-- If the y-computation layer is consistent with `lambda` on wire 0
    and `x₁ - x₃` on wire 1, then output wire 0 equals
    `lambda * (x₁ - x₃)`. -/
theorem yCompute_correct (lambda x1_minus_x3 : F)
    (V_curr V_next : LayerValues F 1)
    (h_in0 : V_next.table wire0 = lambda)
    (h_in1 : V_next.table wire1 = x1_minus_x3)
    (hcons : ∀ g, layerConsistent (yComputeLayer F) V_curr V_next g) :
    V_curr.table wire0 = lambda * x1_minus_x3 := by
  have ⟨hprod, _⟩ := (yComputeLayer_iff V_curr V_next).mp hcons
  rw [hprod, h_in0, h_in1]

-- ============================================================
-- Section 4: Composed point addition correctness
-- ============================================================

/-- End-to-end specification: if the three multiplication layers are
    consistent with appropriate wire assignments, then `ecAddConstraint`
    holds.

    The three layers encode:
    1. Slope: `lambda * (x₂ - x₁) = y₂ - y₁`
    2. Lambda squared: `lambda² = lambda * lambda`
    3. Y computation: `lambda * (x₁ - x₃)`

    The non-multiplication sub-constraints (x₃ and y₃ formulas, infinity
    flags) are passed as direct hypotheses since they are linear relations
    checked outside the multiplication gates. -/
theorem pointAdd_circuit_correct (p1 p2 p3 : ECPoint F) (lambda : F)
    -- Layer 1: Slope verification
    (V1_out V1_in : LayerValues F 1)
    (h_slope_in0 : V1_in.table wire0 = lambda)
    (h_slope_in1 : V1_in.table wire1 = p2.x - p1.x)
    (h_slope_out : V1_out.table wire0 = p2.y - p1.y)
    (hcons1 : ∀ g, layerConsistent (slopeVerifyLayer F) V1_out V1_in g)
    -- Layer 2: Lambda squared
    (V2_out V2_in : LayerValues F 1)
    (h_lsq_in0 : V2_in.table wire0 = lambda)
    (h_lsq_in1 : V2_in.table wire1 = lambda)
    (hcons2 : ∀ g, layerConsistent (lambdaSquaredLayer F) V2_out V2_in g)
    -- Layer 3: Y computation
    (V3_out V3_in : LayerValues F 1)
    (h_ycomp_in0 : V3_in.table wire0 = lambda)
    (h_ycomp_in1 : V3_in.table wire1 = p1.x - p3.x)
    (hcons3 : ∀ g, layerConsistent (yComputeLayer F) V3_out V3_in g)
    -- Linear constraints (checked by the circuit outside mul gates)
    (h_x3 : p3.x = V2_out.table wire0 - p1.x - p2.x)
    (h_y3 : p3.y = V3_out.table wire0 - p1.y)
    -- Infinity flags
    (h_inf1 : p1.is_inf = 0) (h_inf2 : p2.is_inf = 0) (h_inf3 : p3.is_inf = 0) :
    ecAddConstraint p1 p2 p3 lambda := by
  -- Extract multiplication results from layer consistency
  have h_slope := slopeVerify_correct lambda (p2.x - p1.x) (p2.y - p1.y)
    V1_out V1_in h_slope_in0 h_slope_in1 hcons1 h_slope_out
  have h_lsq := lambdaSquared_correct lambda V2_out V2_in h_lsq_in0 h_lsq_in1 hcons2
  have h_yc := yCompute_correct lambda (p1.x - p3.x) V3_out V3_in
    h_ycomp_in0 h_ycomp_in1 hcons3
  -- Assemble ecAddConstraint
  exact ⟨h_inf1, h_inf2, h_inf3, h_slope, by rw [h_x3, h_lsq], by rw [h_y3, h_yc]⟩

/-- Variant of `pointAdd_circuit_correct` using `ecAddFull` for the
    general-addition case. If all three layers are consistent and the
    preconditions for general addition hold (`x₁ ≠ x₂`, both finite),
    then `ecAddFull` is satisfied in the `x₁ ≠ x₂` branch. -/
theorem pointAdd_circuit_ecAddFull (params : CurveParams F)
    (p1 p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    -- ecAddFull requires handling all cases; we provide trivial
    -- witnesses for the branches that are vacuously true.
    (h_inf1 : p1.is_inf = 0) (h_inf2 : p2.is_inf = 0)
    (hne : p1.x ≠ p2.x) :
    ecAddFull params p1 p2 p3 lambda := by
  refine ⟨fun h => absurd (h ▸ h_inf1 : (1 : F) = 0) one_ne_zero,
          fun h => absurd (h ▸ h_inf2 : (1 : F) = 0) one_ne_zero,
          fun _ _ hx _ => absurd hx hne,
          fun _ _ hx _ => absurd hx hne,
          fun _ _ _ => hadd⟩

-- ============================================================
-- Section 5: X-coordinate extraction
-- ============================================================

/-- After point addition yields `R`, the x-coordinate is `R.x`.
    This is definitionally trivial but provides an explicit bridge
    between the EC arithmetic result and the ECDSA x-coordinate check
    (`R.x = r`). -/
theorem xCoord_of_ecAddConstraint (p1 p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddConstraint p1 p2 p3 lambda) :
    p3.x = lambda * lambda - p1.x - p2.x :=
  hadd.2.2.2.2.1

/-- From `ecAddFull` in the general case (`x₁ ≠ x₂`), the result's
    x-coordinate satisfies `R.x = lambda² - x₁ - x₂`. -/
theorem xCoord_of_ecAddFull (params : CurveParams F) (p1 p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddFull params p1 p2 p3 lambda)
    (h_inf1 : p1.is_inf = 0) (h_inf2 : p2.is_inf = 0) (hne : p1.x ≠ p2.x) :
    p3.x = lambda * lambda - p1.x - p2.x :=
  (hadd.2.2.2.2 h_inf1 h_inf2 hne).2.2.2.2.1

/-- The x-coordinate of an `ECPoint` can be directly compared to a
    scalar. This bridges `ecAddConstraint` (which determines `p3.x`)
    and the ECDSA x-coordinate check `R.x = r` (step 7 of
    `ecdsaConstraint`).

    When combined with `xCoord_of_ecAddConstraint`, this gives:
    if `ecAddConstraint` holds then `R.x = lambda² - x₁ - x₂`, so
    checking `R.x = r` amounts to checking `lambda² - x₁ - x₂ = r`. -/
theorem xCoord_eq_of_ecAddConstraint (p1 p2 p3 : ECPoint F) (lambda r : F)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (h_xr : p3.x = r) :
    lambda * lambda - p1.x - p2.x = r := by
  rw [← h_xr]; exact (xCoord_of_ecAddConstraint p1 p2 p3 lambda hadd).symm

-- ============================================================
-- Section 6: Combined point addition and x-extraction
-- ============================================================

/-- Full circuit path for ECDSA steps 6--7: point addition followed by
    x-coordinate extraction. If the three multiplication layers are
    consistent and the linear constraints hold, then the result point
    is not at infinity and its x-coordinate equals `r`. -/
theorem pointAdd_and_xCoord
    (p1 p2 p3 : ECPoint F) (lambda r : F)
    -- Layer 1: Slope verification
    (V1_out V1_in : LayerValues F 1)
    (h_slope_in0 : V1_in.table wire0 = lambda)
    (h_slope_in1 : V1_in.table wire1 = p2.x - p1.x)
    (h_slope_out : V1_out.table wire0 = p2.y - p1.y)
    (hcons1 : ∀ g, layerConsistent (slopeVerifyLayer F) V1_out V1_in g)
    -- Layer 2: Lambda squared
    (V2_out V2_in : LayerValues F 1)
    (h_lsq_in0 : V2_in.table wire0 = lambda)
    (h_lsq_in1 : V2_in.table wire1 = lambda)
    (hcons2 : ∀ g, layerConsistent (lambdaSquaredLayer F) V2_out V2_in g)
    -- Layer 3: Y computation
    (V3_out V3_in : LayerValues F 1)
    (h_ycomp_in0 : V3_in.table wire0 = lambda)
    (h_ycomp_in1 : V3_in.table wire1 = p1.x - p3.x)
    (hcons3 : ∀ g, layerConsistent (yComputeLayer F) V3_out V3_in g)
    -- Linear constraints
    (h_x3 : p3.x = V2_out.table wire0 - p1.x - p2.x)
    (h_y3 : p3.y = V3_out.table wire0 - p1.y)
    -- Infinity flags and x-coordinate
    (h_inf1 : p1.is_inf = 0) (h_inf2 : p2.is_inf = 0) (h_inf3 : p3.is_inf = 0)
    (h_xr : p3.x = r) :
    ecAddConstraint p1 p2 p3 lambda ∧ p3.is_inf = 0 ∧ p3.x = r := by
  exact ⟨pointAdd_circuit_correct p1 p2 p3 lambda
    V1_out V1_in h_slope_in0 h_slope_in1 h_slope_out hcons1
    V2_out V2_in h_lsq_in0 h_lsq_in1 hcons2
    V3_out V3_in h_ycomp_in0 h_ycomp_in1 hcons3
    h_x3 h_y3 h_inf1 h_inf2 h_inf3, h_inf3, h_xr⟩
