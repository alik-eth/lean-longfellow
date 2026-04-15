import LeanLongfellow.Circuit.GateCircuit
import LeanLongfellow.Circuit.ECDSAGateFieldOps
import LeanLongfellow.Circuit.ECDSAGateScalarMul
import LeanLongfellow.Circuit.ECDSAGatePointAdd
import LeanLongfellow.Circuit.ECDSA
import LeanLongfellow.Circuit.ECDSACircuit

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Gate-Level Circuit Composition

Assembles all four phases of the gate-level ECDSA verification circuit
into a single layer sequence and defines the concrete `ECDSACircuitSpec`.

## Circuit Layout (layers numbered from top = 0 to bottom = NL)

The circuit has `14n + 7` layers for `n`-bit scalar multiplication:

| Phase | Layers (from top) | Count | Purpose |
|-------|-------------------|-------|---------|
| D     | 0                 | 1     | Equality check: `(R.x - r)²` |
| C     | 1–3               | 3     | Point addition: `R = P1 + P2` |
| B2    | 4 to 4+7n-1       | 7n    | Scalar mul: `u2 · Q` |
| B1    | 4+7n to 4+14n-1   | 7n    | Scalar mul: `u1 · G` |
| A     | 4+14n to 4+14n+2  | 3     | Field ops: `s_inv`, `u1`, `u2` |

The verifier checks from top to bottom; the prover fills in from bottom
to top. Layer 0 is the "output" layer.
-/

variable (F : Type*) [Field F]

-- ============================================================
-- Section 1: Phase D — Equality check layer
-- ============================================================

/-- Passthroughs for the equality check layer (all non-zero wires except W_OUTPUT). -/
def equalityPassthroughs : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK]

/-- Equality check layer: computes `(R.x - r)²` at W_OUTPUT.
    W_TEMP1 holds `(R.x - r)` as a prover-supplied witness. -/
def equalityCheckLayer : CircuitLayer F 5 :=
  mulPassLayer F W_OUTPUT W_TEMP1 W_TEMP1 equalityPassthroughs

-- ============================================================
-- Section 1a: Distinctness and precondition lemmas for equality layer
-- ============================================================

private theorem wirePos_ne (a b : ℕ) (ha : a < 32) (hb : b < 32) (hab : a ≠ b) :
    wirePos a ≠ wirePos b := by
  intro h
  have := wirePos_injective ⟨a, ha⟩ ⟨b, hb⟩ h
  exact hab (Fin.val_eq_of_eq this)

private theorem W_OUTPUT_ne_ZERO : W_OUTPUT ≠ W_ZERO :=
  wirePos_ne 31 0 (by omega) (by omega) (by omega)

private theorem eqPass_ne_zero :
    ∀ p ∈ equalityPassthroughs, p ≠ W_ZERO := by native_decide

private theorem eqPass_ne_out :
    ∀ p ∈ equalityPassthroughs, p ≠ W_OUTPUT := by native_decide

private theorem eqPass_nodup :
    equalityPassthroughs.Nodup := by native_decide

-- ============================================================
-- Section 1b: Equality layer semantics
-- ============================================================

/-- Bidirectional semantics for the equality check layer. -/
theorem equalityCheckLayer_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (equalityCheckLayer F) V_curr V_next g) ↔
    (V_curr.table W_OUTPUT = V_next.table W_TEMP1 * V_next.table W_TEMP1 ∧
     (∀ p ∈ equalityPassthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_OUTPUT → q ∉ equalityPassthroughs → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_OUTPUT W_TEMP1 W_TEMP1 equalityPassthroughs V_curr V_next
    W_OUTPUT_ne_ZERO eqPass_ne_zero eqPass_ne_out eqPass_nodup

-- ============================================================
-- Section 2: Full layer count and layer sequence
-- ============================================================

/-- Total number of layers in the gate-level ECDSA circuit with `n`-bit scalars.
    = 1 (equality) + 3 (point add) + 7n (scalar mul 2) + 7n (scalar mul 1) + 3 (field ops)
    = 14n + 7 -/
def ecdsaGateNL (n : ℕ) : ℕ := 14 * n + 7

/-- The full gate-level ECDSA layer sequence.

    Layout (top to bottom):
    - Layer 0:                  equality check (Phase D)
    - Layers 1..3:              point addition (Phase C)
    - Layers 4..4+7n-1:         scalar mul chain 2, u₂·Q (Phase B2)
    - Layers 4+7n..4+14n-1:     scalar mul chain 1, u₁·G (Phase B1)
    - Layers 4+14n..4+14n+2:    field operations (Phase A) -/
noncomputable def ecdsaGateLayers
    (n : ℕ) : Fin (ecdsaGateNL n) → CircuitLayer F 5 :=
  fun idx =>
    if idx.val = 0 then
      -- Phase D: equality check
      equalityCheckLayer F
    else if idx.val ≤ 3 then
      -- Phase C: point addition (layers 1, 2, 3)
      -- layer 1 -> pointAdd_layer0, layer 2 -> pointAdd_layer1, layer 3 -> pointAdd_layer2
      match idx.val - 1 with
      | 0 => pointAdd_layer0 F
      | 1 => pointAdd_layer1 F
      | _ => pointAdd_layer2 F
    else if idx.val < 4 + 7 * n then
      -- Phase B2: scalar mul chain 2 (u₂·Q), layers 4 to 4+7n-1
      let offset := idx.val - 4
      scalarMulStepLayers F ⟨offset % 7, Nat.mod_lt offset (by omega)⟩
    else if idx.val < 4 + 14 * n then
      -- Phase B1: scalar mul chain 1 (u₁·G), layers 4+7n to 4+14n-1
      let offset := idx.val - (4 + 7 * n)
      scalarMulStepLayers F ⟨offset % 7, Nat.mod_lt offset (by omega)⟩
    else
      -- Phase A: field operations (layers 4+14n, 4+14n+1, 4+14n+2)
      match idx.val - (4 + 14 * n) with
      | 0 => fieldOps_invCheck F
      | 1 => fieldOps_u1 F
      | _ => fieldOps_u2 F

-- ============================================================
-- Section 3: ECDSACircuitSpec instance
-- ============================================================

/-- The concrete gate-level ECDSA circuit specification.

    This bundles the layer sequence with the extraction property:
    if all layers are consistent and the output evaluates to 1,
    then ECDSA verifies.

    **Trusted hypothesis (`hverify`).**  The gate-level circuit defined by
    `ecdsaGateLayers` checks only multiplication sub-constraints (one
    quadratic equation per layer).  The full ECDSA constraint additionally
    requires:

    * Linear coordinate formulas inside `ecDoubleConstraint` / `ecAddFull`
      (slope equations, x₃/y₃ expressions).
    * Identity initialisation (`intermediates 0 = ⟨0,0,1⟩`) for each
      scalar-multiplication chain.
    * Public-input encoding: the bottom-layer wire values must match
      `sig.s`, `z`, and `sig.r`.
    * Non-zero check: `sig.s ≠ 0` (no gate layer enforces invertibility).

    Because the gate layers do not encode the public inputs (`z`, `Q`,
    `sig`) — every layer is a generic `mulPassLayer` — the extraction
    cannot derive `ecdsaVerify z Q sig` from layer consistency alone.
    The `hverify` hypothesis fills this gap.

    Eliminating `hverify` requires either:
    (a) extending the layer sequence with linear-constraint gates and
        public-input-encoding layers, or
    (b) embedding `z`, `Q`, `sig` into the layer polynomials (as done
        by `ecdsaCircuitSpec` in `ECDSAComposition.lean`).

    The gate infrastructure (field ops, scalar mul, point add, equality
    check phases and their extraction theorems) is fully proven and
    ready to support approach (a) when additional layers are added. -/
noncomputable def ecdsaGateCircuitSpec [EllipticCurve F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (n : ℕ)
    (hverify : ecdsaVerify z Q sig) : ECDSACircuitSpec F 5 (ecdsaGateNL n) z Q sig where
  layers := ecdsaGateLayers F n
  extraction := fun _ _ _ _ => hverify

-- ============================================================
-- Section 4: Basic properties
-- ============================================================

/-- The gate-level ECDSA circuit has the expected number of layers. -/
theorem ecdsaGateNL_eq (n : ℕ) : ecdsaGateNL n = 14 * n + 7 := rfl

/-- The equality check layer is the first (top) layer. -/
theorem ecdsaGateLayers_zero (n : ℕ) (h : 0 < ecdsaGateNL n) :
    ecdsaGateLayers F n ⟨0, h⟩ = equalityCheckLayer F := by
  simp [ecdsaGateLayers]

/-- The zero wire is uncovered in the equality check layer. -/
theorem equalityCheck_zero_wire (V_curr V_next : LayerValues F 5)
    (hcons : ∀ g, layerConsistent (equalityCheckLayer F) V_curr V_next g) :
    V_curr.table W_ZERO = 0 :=
  ((equalityCheckLayer_iff F V_curr V_next).mp hcons).2.2.1
