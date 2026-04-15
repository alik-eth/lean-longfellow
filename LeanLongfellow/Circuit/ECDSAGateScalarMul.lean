import LeanLongfellow.Circuit.GateCircuit
import LeanLongfellow.Circuit.ECArith

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Gate-Level Scalar Multiplication (Phase B)

Six `mulPassLayer` layers per scalar multiplication step, verifying the
multiplication constraints arising from point doubling and conditional addition.

Each step of `ecScalarMulChain` requires:
- **Doubling** (`ecDoubleConstraint`): 3 multiplications
  1. `acc_x * acc_x` (for `3x_1^2 + a` in slope check)
  2. `lambda_d * lambda_d` (for `x_3 = lambda^2 - 2x_1`)
  3. `lambda_d * temp4` (for `y_3 = lambda * (x_1 - x_3) - y_1`, where `temp4 = x_1 - x_3`)
- **Addition** (`ecAddConstraint` within `ecCondAdd`): 3 multiplications
  4. `lambda_a * temp5` (for slope check: `lambda * (x_2 - x_1) = y_2 - y_1`)
  5. `lambda_a * lambda_a` (for `x_3 = lambda^2 - x_1 - x_2`)
  6. `lambda_a * acc_x` (for `y_3 = lambda * (x_1 - x_3) - y_1`,
     where `acc_x` holds `x_1 - x_3` at this point)

The prover places all intermediate values on the 32 wires; the circuit (verifier)
checks one multiplication equation per layer.

## Wire layout

```
W_ACC_X (4), W_ACC_Y (5), W_ACC_INF (6)   -- accumulator point
W_DBL_X (7), W_DBL_Y (8), W_DBL_INF (9)   -- doubled point
W_PX (10), W_PY (11)                        -- base point P
W_BIT (12)                                   -- current scalar bit
W_LAMBDA_D (13)                              -- doubling slope
W_LAMBDA_A (14)                              -- addition slope
W_TEMP1 (15), W_TEMP2 (16), W_TEMP3 (17)   -- temporaries for mul outputs
W_TEMP4 (28), W_TEMP5 (29)                  -- prover-supplied differences
```
-/

variable (F : Type*) [Field F]

-- ============================================================
-- Section 1: Passthrough lists for each scalar mul layer
-- ============================================================

/-- All 31 non-zero wire positions (1..31). -/
private def allNonZero31 : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 0 (doubling: acc_x * acc_x -> temp1).
    All non-zero wires except W_TEMP1. -/
def smLayer0Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 1 (doubling: lambda_d * lambda_d -> temp2).
    All non-zero wires except W_TEMP2. -/
def smLayer1Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 2 (doubling: lambda_d * temp4 -> temp3).
    All non-zero wires except W_TEMP3. -/
def smLayer2Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 3 (addition: lambda_a * temp5 -> temp1).
    All non-zero wires except W_TEMP1. -/
def smLayer3Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 4 (addition: lambda_a * lambda_a -> temp2).
    All non-zero wires except W_TEMP2. -/
def smLayer4Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

/-- Passthroughs for layer 5 (addition: lambda_a * acc_x -> temp3).
    All non-zero wires except W_TEMP3. -/
def smLayer5Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_ZCHECK, W_OUTPUT]

-- ============================================================
-- Section 2: Layer definitions
-- ============================================================

/-- Layer 0: Doubling step 1 -- `acc_x * acc_x -> temp1`.
    Computes `x_1^2` needed for the slope numerator `3x_1^2 + a`. -/
def smLayer0 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP1 W_ACC_X W_ACC_X smLayer0Pass

/-- Layer 1: Doubling step 2 -- `lambda_d * lambda_d -> temp2`.
    Computes `lambda_d^2` needed for `x_3 = lambda_d^2 - 2x_1`. -/
def smLayer1 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP2 W_LAMBDA_D W_LAMBDA_D smLayer1Pass

/-- Layer 2: Doubling step 3 -- `lambda_d * temp4 -> temp3`.
    Computes `lambda_d * (x_1 - x_3)` needed for `y_3 = lambda_d(x_1 - x_3) - y_1`,
    where `temp4` holds the prover-supplied difference `x_1 - x_3`. -/
def smLayer2 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP3 W_LAMBDA_D W_TEMP4 smLayer2Pass

/-- Layer 3: Addition step 1 -- `lambda_a * temp5 -> temp1`.
    Computes `lambda_a * (x_2 - x_1)` for the addition slope check,
    where `temp5` holds the prover-supplied difference `x_2 - x_1`. -/
def smLayer3 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP1 W_LAMBDA_A W_TEMP5 smLayer3Pass

/-- Layer 4: Addition step 2 -- `lambda_a * lambda_a -> temp2`.
    Computes `lambda_a^2` needed for `x_3 = lambda_a^2 - x_1 - x_2`. -/
def smLayer4 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP2 W_LAMBDA_A W_LAMBDA_A smLayer4Pass

/-- Layer 5: Addition step 3 -- `lambda_a * acc_x -> temp3`.
    Computes `lambda_a * (x_1 - x_3)` for `y_3 = lambda_a(x_1 - x_3) - y_1`,
    where `acc_x` holds `x_1 - x_3` at this stage (prover-managed). -/
def smLayer5 : CircuitLayer F 5 :=
  mulPassLayer F W_TEMP3 W_LAMBDA_A W_ACC_X smLayer5Pass

-- ============================================================
-- Section 3: The 6-layer step bundle
-- ============================================================

/-- The 6 layers for one scalar multiplication step (doubling + conditional add). -/
def scalarMulStepLayers : Fin 6 → CircuitLayer F 5
  | ⟨0, _⟩ => smLayer0 F
  | ⟨1, _⟩ => smLayer1 F
  | ⟨2, _⟩ => smLayer2 F
  | ⟨3, _⟩ => smLayer3 F
  | ⟨4, _⟩ => smLayer4 F
  | ⟨5, _⟩ => smLayer5 F

/-- All layers for `n` scalar multiplication steps: `6*n` layers total.
    Step `k` uses layers `6*k` through `6*k+5`. -/
def scalarMulAllLayers (n : ℕ) : Fin (6 * n) → CircuitLayer F 5 :=
  fun ⟨i, hi⟩ =>
    scalarMulStepLayers F ⟨i % 6, Nat.mod_lt i (by omega)⟩

-- ============================================================
-- Section 4: Distinctness and precondition lemmas
-- ============================================================

-- Wire distinctness for output positions
private theorem W_TEMP1_ne_ZERO' : W_TEMP1 ≠ W_ZERO := by native_decide
private theorem W_TEMP2_ne_ZERO : W_TEMP2 ≠ W_ZERO := by native_decide
private theorem W_TEMP3_ne_ZERO : W_TEMP3 ≠ W_ZERO := by native_decide

-- Layer 0 preconditions
private theorem smL0_pass_ne_zero : ∀ p ∈ smLayer0Pass, p ≠ W_ZERO := by native_decide
private theorem smL0_pass_ne_out : ∀ p ∈ smLayer0Pass, p ≠ W_TEMP1 := by native_decide
private theorem smL0_pass_nodup : smLayer0Pass.Nodup := by native_decide

-- Layer 1 preconditions
private theorem smL1_pass_ne_zero : ∀ p ∈ smLayer1Pass, p ≠ W_ZERO := by native_decide
private theorem smL1_pass_ne_out : ∀ p ∈ smLayer1Pass, p ≠ W_TEMP2 := by native_decide
private theorem smL1_pass_nodup : smLayer1Pass.Nodup := by native_decide

-- Layer 2 preconditions
private theorem smL2_pass_ne_zero : ∀ p ∈ smLayer2Pass, p ≠ W_ZERO := by native_decide
private theorem smL2_pass_ne_out : ∀ p ∈ smLayer2Pass, p ≠ W_TEMP3 := by native_decide
private theorem smL2_pass_nodup : smLayer2Pass.Nodup := by native_decide

-- Layer 3 preconditions
private theorem smL3_pass_ne_zero : ∀ p ∈ smLayer3Pass, p ≠ W_ZERO := by native_decide
private theorem smL3_pass_ne_out : ∀ p ∈ smLayer3Pass, p ≠ W_TEMP1 := by native_decide
private theorem smL3_pass_nodup : smLayer3Pass.Nodup := by native_decide

-- Layer 4 preconditions
private theorem smL4_pass_ne_zero : ∀ p ∈ smLayer4Pass, p ≠ W_ZERO := by native_decide
private theorem smL4_pass_ne_out : ∀ p ∈ smLayer4Pass, p ≠ W_TEMP2 := by native_decide
private theorem smL4_pass_nodup : smLayer4Pass.Nodup := by native_decide

-- Layer 5 preconditions
private theorem smL5_pass_ne_zero : ∀ p ∈ smLayer5Pass, p ≠ W_ZERO := by native_decide
private theorem smL5_pass_ne_out : ∀ p ∈ smLayer5Pass, p ≠ W_TEMP3 := by native_decide
private theorem smL5_pass_nodup : smLayer5Pass.Nodup := by native_decide

-- ============================================================
-- Section 5: Per-layer bidirectional semantics
-- ============================================================

/-- Layer 0 semantics: `V_curr(W_TEMP1) = V_next(W_ACC_X) * V_next(W_ACC_X)`. -/
theorem smLayer0_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer0 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP1 = V_next.table W_ACC_X * V_next.table W_ACC_X ∧
     (∀ p ∈ smLayer0Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP1 → q ∉ smLayer0Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP1 W_ACC_X W_ACC_X smLayer0Pass V_curr V_next
    W_TEMP1_ne_ZERO' smL0_pass_ne_zero smL0_pass_ne_out smL0_pass_nodup

/-- Layer 1 semantics: `V_curr(W_TEMP2) = V_next(W_LAMBDA_D) * V_next(W_LAMBDA_D)`. -/
theorem smLayer1_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer1 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP2 = V_next.table W_LAMBDA_D * V_next.table W_LAMBDA_D ∧
     (∀ p ∈ smLayer1Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP2 → q ∉ smLayer1Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP2 W_LAMBDA_D W_LAMBDA_D smLayer1Pass V_curr V_next
    W_TEMP2_ne_ZERO smL1_pass_ne_zero smL1_pass_ne_out smL1_pass_nodup

/-- Layer 2 semantics: `V_curr(W_TEMP3) = V_next(W_LAMBDA_D) * V_next(W_TEMP4)`. -/
theorem smLayer2_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer2 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP3 = V_next.table W_LAMBDA_D * V_next.table W_TEMP4 ∧
     (∀ p ∈ smLayer2Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP3 → q ∉ smLayer2Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP3 W_LAMBDA_D W_TEMP4 smLayer2Pass V_curr V_next
    W_TEMP3_ne_ZERO smL2_pass_ne_zero smL2_pass_ne_out smL2_pass_nodup

/-- Layer 3 semantics: `V_curr(W_TEMP1) = V_next(W_LAMBDA_A) * V_next(W_TEMP5)`. -/
theorem smLayer3_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer3 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP1 = V_next.table W_LAMBDA_A * V_next.table W_TEMP5 ∧
     (∀ p ∈ smLayer3Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP1 → q ∉ smLayer3Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP1 W_LAMBDA_A W_TEMP5 smLayer3Pass V_curr V_next
    W_TEMP1_ne_ZERO' smL3_pass_ne_zero smL3_pass_ne_out smL3_pass_nodup

/-- Layer 4 semantics: `V_curr(W_TEMP2) = V_next(W_LAMBDA_A) * V_next(W_LAMBDA_A)`. -/
theorem smLayer4_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer4 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP2 = V_next.table W_LAMBDA_A * V_next.table W_LAMBDA_A ∧
     (∀ p ∈ smLayer4Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP2 → q ∉ smLayer4Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP2 W_LAMBDA_A W_LAMBDA_A smLayer4Pass V_curr V_next
    W_TEMP2_ne_ZERO smL4_pass_ne_zero smL4_pass_ne_out smL4_pass_nodup

/-- Layer 5 semantics: `V_curr(W_TEMP3) = V_next(W_LAMBDA_A) * V_next(W_ACC_X)`. -/
theorem smLayer5_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer5 F) V_curr V_next g) ↔
    (V_curr.table W_TEMP3 = V_next.table W_LAMBDA_A * V_next.table W_ACC_X ∧
     (∀ p ∈ smLayer5Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_TEMP3 → q ∉ smLayer5Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_TEMP3 W_LAMBDA_A W_ACC_X smLayer5Pass V_curr V_next
    W_TEMP3_ne_ZERO smL5_pass_ne_zero smL5_pass_ne_out smL5_pass_nodup

-- ============================================================
-- Section 6: Passthrough membership lemmas
-- ============================================================

-- Wires that pass through all 6 layers (needed for value propagation)

-- W_ACC_X passes through layers 1-5 (consumed by layer 0 as input, but passes through others)
private theorem W_ACC_X_in_smL1 : W_ACC_X ∈ smLayer1Pass := by native_decide
private theorem W_ACC_X_in_smL2 : W_ACC_X ∈ smLayer2Pass := by native_decide
private theorem W_ACC_X_in_smL3 : W_ACC_X ∈ smLayer3Pass := by native_decide
private theorem W_ACC_X_in_smL4 : W_ACC_X ∈ smLayer4Pass := by native_decide
-- W_ACC_X is used as a right input in layer 5, but still passes through:
private theorem W_ACC_X_in_smL5 : W_ACC_X ∈ smLayer5Pass := by native_decide

-- W_LAMBDA_D passes through layers 0, 3, 4, 5
private theorem W_LAMBDA_D_in_smL0 : W_LAMBDA_D ∈ smLayer0Pass := by native_decide
private theorem W_LAMBDA_D_in_smL3 : W_LAMBDA_D ∈ smLayer3Pass := by native_decide
private theorem W_LAMBDA_D_in_smL4 : W_LAMBDA_D ∈ smLayer4Pass := by native_decide
private theorem W_LAMBDA_D_in_smL5 : W_LAMBDA_D ∈ smLayer5Pass := by native_decide

-- W_LAMBDA_A passes through layers 0, 1, 2
private theorem W_LAMBDA_A_in_smL0 : W_LAMBDA_A ∈ smLayer0Pass := by native_decide
private theorem W_LAMBDA_A_in_smL1 : W_LAMBDA_A ∈ smLayer1Pass := by native_decide
private theorem W_LAMBDA_A_in_smL2 : W_LAMBDA_A ∈ smLayer2Pass := by native_decide

-- W_TEMP4 passes through layers 0, 1, 3, 4, 5
private theorem W_TEMP4_in_smL0 : W_TEMP4 ∈ smLayer0Pass := by native_decide
private theorem W_TEMP4_in_smL1 : W_TEMP4 ∈ smLayer1Pass := by native_decide
private theorem W_TEMP4_in_smL3 : W_TEMP4 ∈ smLayer3Pass := by native_decide
private theorem W_TEMP4_in_smL4 : W_TEMP4 ∈ smLayer4Pass := by native_decide
private theorem W_TEMP4_in_smL5 : W_TEMP4 ∈ smLayer5Pass := by native_decide

-- W_TEMP5 passes through layers 0, 1, 2, 4, 5
private theorem W_TEMP5_in_smL0 : W_TEMP5 ∈ smLayer0Pass := by native_decide
private theorem W_TEMP5_in_smL1 : W_TEMP5 ∈ smLayer1Pass := by native_decide
private theorem W_TEMP5_in_smL2 : W_TEMP5 ∈ smLayer2Pass := by native_decide
private theorem W_TEMP5_in_smL4 : W_TEMP5 ∈ smLayer4Pass := by native_decide
private theorem W_TEMP5_in_smL5 : W_TEMP5 ∈ smLayer5Pass := by native_decide

-- W_ACC_Y passes through all layers
private theorem W_ACC_Y_in_smL0 : W_ACC_Y ∈ smLayer0Pass := by native_decide
private theorem W_ACC_Y_in_smL1 : W_ACC_Y ∈ smLayer1Pass := by native_decide
private theorem W_ACC_Y_in_smL2 : W_ACC_Y ∈ smLayer2Pass := by native_decide
private theorem W_ACC_Y_in_smL3 : W_ACC_Y ∈ smLayer3Pass := by native_decide
private theorem W_ACC_Y_in_smL4 : W_ACC_Y ∈ smLayer4Pass := by native_decide
private theorem W_ACC_Y_in_smL5 : W_ACC_Y ∈ smLayer5Pass := by native_decide

-- W_ACC_X passes through layer 0 (it is the input, but it's still in the passthrough list)
private theorem W_ACC_X_in_smL0 : W_ACC_X ∈ smLayer0Pass := by native_decide

-- ============================================================
-- Section 7: Zero wire propagation
-- ============================================================

/-- Zero wire is zero at every layer boundary of a consistent scalar mul step. -/
theorem smStep_zero_wire_chain
    (values : Fin 7 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (_hzero6 : (values 6).table W_ZERO = 0) :
    (values 5).table W_ZERO = 0 ∧
    (values 4).table W_ZERO = 0 ∧
    (values 3).table W_ZERO = 0 ∧
    (values 2).table W_ZERO = 0 ∧
    (values 1).table W_ZERO = 0 ∧
    (values 0).table W_ZERO = 0 := by
  have hz5 := ((smLayer5_iff F (values 5) (values 6)).mp hcons5).2.2.1
  have hz4 := ((smLayer4_iff F (values 4) (values 5)).mp hcons4).2.2.1
  have hz3 := ((smLayer3_iff F (values 3) (values 4)).mp hcons3).2.2.1
  have hz2 := ((smLayer2_iff F (values 2) (values 3)).mp hcons2).2.2.1
  have hz1 := ((smLayer1_iff F (values 1) (values 2)).mp hcons1).2.2.1
  have hz0 := ((smLayer0_iff F (values 0) (values 1)).mp hcons0).2.2.1
  exact ⟨hz5, hz4, hz3, hz2, hz1, hz0⟩

-- ============================================================
-- Section 8: One-step multiplication equations extraction
-- ============================================================

/-- **Scalar mul step extraction**: from layer consistency of the 6 layers
    in one scalar multiplication step, extract the 6 multiplication equations.

    The wires carrying `lambda_d`, `lambda_a`, `acc_x`, `temp4`, `temp5` are traced
    back through passthrough gates to the bottom layer (values 6), yielding:

    1. `V_0(W_TEMP1) = V_6(W_ACC_X)^2`
    2. `V_1(W_TEMP2) = V_6(W_LAMBDA_D)^2`
    3. `V_2(W_TEMP3) = V_6(W_LAMBDA_D) * V_6(W_TEMP4)`
    4. `V_3(W_TEMP1) = V_6(W_LAMBDA_A) * V_6(W_TEMP5)`
    5. `V_4(W_TEMP2) = V_6(W_LAMBDA_A)^2`
    6. `V_5(W_TEMP3) = V_6(W_LAMBDA_A) * V_6(W_ACC_X)` -/
theorem scalarMul_step_mul_equations
    (values : Fin 7 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (hzero6 : (values 6).table W_ZERO = 0) :
    -- Doubling multiplications
    (values 0).table W_TEMP1 = (values 6).table W_ACC_X * (values 6).table W_ACC_X ∧
    (values 1).table W_TEMP2 = (values 6).table W_LAMBDA_D * (values 6).table W_LAMBDA_D ∧
    (values 2).table W_TEMP3 = (values 6).table W_LAMBDA_D * (values 6).table W_TEMP4 ∧
    -- Addition multiplications
    (values 3).table W_TEMP1 = (values 6).table W_LAMBDA_A * (values 6).table W_TEMP5 ∧
    (values 4).table W_TEMP2 = (values 6).table W_LAMBDA_A * (values 6).table W_LAMBDA_A ∧
    (values 5).table W_TEMP3 = (values 6).table W_LAMBDA_A * (values 6).table W_ACC_X := by
  -- Extract per-layer semantics
  have h0 := (smLayer0_iff F (values 0) (values 1)).mp hcons0
  have h1 := (smLayer1_iff F (values 1) (values 2)).mp hcons1
  have h2 := (smLayer2_iff F (values 2) (values 3)).mp hcons2
  have h3 := (smLayer3_iff F (values 3) (values 4)).mp hcons3
  have h4 := (smLayer4_iff F (values 4) (values 5)).mp hcons4
  have h5 := (smLayer5_iff F (values 5) (values 6)).mp hcons5
  -- Extract zero-wire facts
  have ⟨hz5, hz4, hz3, hz2, hz1, _⟩ :=
    smStep_zero_wire_chain F values hcons0 hcons1 hcons2 hcons3 hcons4 hcons5 hzero6
  -- Extract mul equations and passthrough equations
  obtain ⟨hmul0, hpass0, _, _⟩ := h0
  obtain ⟨hmul1, hpass1, _, _⟩ := h1
  obtain ⟨hmul2, hpass2, _, _⟩ := h2
  obtain ⟨hmul3, hpass3, _, _⟩ := h3
  obtain ⟨hmul4, hpass4, _, _⟩ := h4
  obtain ⟨hmul5, hpass5, _, _⟩ := h5
  -- Trace W_ACC_X from layer 1 back to layer 6
  have haccx_12 : (values 1).table W_ACC_X = (values 2).table W_ACC_X :=
    passthrough_exact (hpass1 W_ACC_X W_ACC_X_in_smL1) hz2
  have haccx_23 : (values 2).table W_ACC_X = (values 3).table W_ACC_X :=
    passthrough_exact (hpass2 W_ACC_X W_ACC_X_in_smL2) hz3
  have haccx_34 : (values 3).table W_ACC_X = (values 4).table W_ACC_X :=
    passthrough_exact (hpass3 W_ACC_X W_ACC_X_in_smL3) hz4
  have haccx_45 : (values 4).table W_ACC_X = (values 5).table W_ACC_X :=
    passthrough_exact (hpass4 W_ACC_X W_ACC_X_in_smL4) hz5
  have haccx_56 : (values 5).table W_ACC_X = (values 6).table W_ACC_X :=
    passthrough_exact (hpass5 W_ACC_X W_ACC_X_in_smL5) hzero6
  -- Trace W_LAMBDA_D from layer 1 back to layer 6
  -- Layer 1 consumes W_LAMBDA_D, but passes it through layer 0
  -- Actually W_LAMBDA_D passes through layers 0, then is consumed in 1, 2
  -- but it's in the passthrough lists for all layers
  have hld_12 : (values 1).table W_LAMBDA_D = (values 2).table W_LAMBDA_D :=
    passthrough_exact (hpass1 W_LAMBDA_D (by native_decide)) hz2
  have hld_23 : (values 2).table W_LAMBDA_D = (values 3).table W_LAMBDA_D :=
    passthrough_exact (hpass2 W_LAMBDA_D (by native_decide)) hz3
  have hld_34 : (values 3).table W_LAMBDA_D = (values 4).table W_LAMBDA_D :=
    passthrough_exact (hpass3 W_LAMBDA_D W_LAMBDA_D_in_smL3) hz4
  have hld_45 : (values 4).table W_LAMBDA_D = (values 5).table W_LAMBDA_D :=
    passthrough_exact (hpass4 W_LAMBDA_D W_LAMBDA_D_in_smL4) hz5
  have hld_56 : (values 5).table W_LAMBDA_D = (values 6).table W_LAMBDA_D :=
    passthrough_exact (hpass5 W_LAMBDA_D W_LAMBDA_D_in_smL5) hzero6
  -- Trace W_TEMP4 from layer 1 back to layer 6
  have ht4_12 : (values 1).table W_TEMP4 = (values 2).table W_TEMP4 :=
    passthrough_exact (hpass1 W_TEMP4 W_TEMP4_in_smL1) hz2
  have ht4_23 : (values 2).table W_TEMP4 = (values 3).table W_TEMP4 :=
    passthrough_exact (hpass2 W_TEMP4 (by native_decide)) hz3
  have ht4_34 : (values 3).table W_TEMP4 = (values 4).table W_TEMP4 :=
    passthrough_exact (hpass3 W_TEMP4 W_TEMP4_in_smL3) hz4
  have ht4_45 : (values 4).table W_TEMP4 = (values 5).table W_TEMP4 :=
    passthrough_exact (hpass4 W_TEMP4 W_TEMP4_in_smL4) hz5
  have ht4_56 : (values 5).table W_TEMP4 = (values 6).table W_TEMP4 :=
    passthrough_exact (hpass5 W_TEMP4 W_TEMP4_in_smL5) hzero6
  -- Trace W_LAMBDA_A from layer 1 back to layer 6
  have hla_12 : (values 1).table W_LAMBDA_A = (values 2).table W_LAMBDA_A :=
    passthrough_exact (hpass1 W_LAMBDA_A W_LAMBDA_A_in_smL1) hz2
  have hla_23 : (values 2).table W_LAMBDA_A = (values 3).table W_LAMBDA_A :=
    passthrough_exact (hpass2 W_LAMBDA_A W_LAMBDA_A_in_smL2) hz3
  have hla_34 : (values 3).table W_LAMBDA_A = (values 4).table W_LAMBDA_A :=
    passthrough_exact (hpass3 W_LAMBDA_A (by native_decide)) hz4
  have hla_45 : (values 4).table W_LAMBDA_A = (values 5).table W_LAMBDA_A :=
    passthrough_exact (hpass4 W_LAMBDA_A (by native_decide)) hz5
  have hla_56 : (values 5).table W_LAMBDA_A = (values 6).table W_LAMBDA_A :=
    passthrough_exact (hpass5 W_LAMBDA_A (by native_decide)) hzero6
  -- Trace W_TEMP5 from layer 1 back to layer 6
  have ht5_12 : (values 1).table W_TEMP5 = (values 2).table W_TEMP5 :=
    passthrough_exact (hpass1 W_TEMP5 W_TEMP5_in_smL1) hz2
  have ht5_23 : (values 2).table W_TEMP5 = (values 3).table W_TEMP5 :=
    passthrough_exact (hpass2 W_TEMP5 W_TEMP5_in_smL2) hz3
  have ht5_34 : (values 3).table W_TEMP5 = (values 4).table W_TEMP5 :=
    passthrough_exact (hpass3 W_TEMP5 (by native_decide)) hz4
  have ht5_45 : (values 4).table W_TEMP5 = (values 5).table W_TEMP5 :=
    passthrough_exact (hpass4 W_TEMP5 W_TEMP5_in_smL4) hz5
  have ht5_56 : (values 5).table W_TEMP5 = (values 6).table W_TEMP5 :=
    passthrough_exact (hpass5 W_TEMP5 W_TEMP5_in_smL5) hzero6
  -- Assemble all 6 equations
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Equation 1: V_0(W_TEMP1) = V_6(W_ACC_X)^2
    rw [hmul0]
    -- V_1(W_ACC_X) = V_6(W_ACC_X) by tracing through layers 1-6
    rw [haccx_12, haccx_23, haccx_34, haccx_45, haccx_56]
  · -- Equation 2: V_1(W_TEMP2) = V_6(W_LAMBDA_D)^2
    rw [hmul1]
    rw [hld_23, hld_34, hld_45, hld_56]
  · -- Equation 3: V_2(W_TEMP3) = V_6(W_LAMBDA_D) * V_6(W_TEMP4)
    rw [hmul2]
    rw [hld_34, hld_45, hld_56]
    rw [ht4_34, ht4_45, ht4_56]
  · -- Equation 4: V_3(W_TEMP1) = V_6(W_LAMBDA_A) * V_6(W_TEMP5)
    rw [hmul3]
    rw [hla_45, hla_56]
    rw [ht5_45, ht5_56]
  · -- Equation 5: V_4(W_TEMP2) = V_6(W_LAMBDA_A)^2
    rw [hmul4]
    rw [hla_56]
  · -- Equation 6: V_5(W_TEMP3) = V_6(W_LAMBDA_A) * V_6(W_ACC_X)
    rw [hmul5]

-- ============================================================
-- Section 9: Wire-reading interface for scalar mul step
-- ============================================================

/-- Read EC point coordinates and witness values from the bottom layer of a step.
    This packages wire values into the `ECPoint` and scalar data needed by
    `ecScalarMulChain`. -/
structure ScalarMulStepWires (F : Type*) [Field F] where
  /-- Accumulator point (input to this step). -/
  acc : ECPoint F
  /-- Doubled point (output of doubling). -/
  dbl : ECPoint F
  /-- Base point P. -/
  baseP : ECPoint F
  /-- Current scalar bit. -/
  bit : F
  /-- Doubling slope witness. -/
  lambda_d : F
  /-- Addition slope witness. -/
  lambda_a : F
  /-- Temporary: x_1 - x_3 for doubling. -/
  dbl_diff : F
  /-- Temporary: x_2 - x_1 for addition. -/
  add_diff : F

/-- Extract `ScalarMulStepWires` from wire values at the bottom layer of a step. -/
def readStepWires (V : LayerValues F 5) : ScalarMulStepWires F :=
  { acc := ⟨V.table W_ACC_X, V.table W_ACC_Y, V.table W_ACC_INF⟩
    dbl := ⟨V.table W_DBL_X, V.table W_DBL_Y, V.table W_DBL_INF⟩
    baseP := ⟨V.table W_PX, V.table W_PY, 0⟩  -- base point assumed finite
    bit := V.table W_BIT
    lambda_d := V.table W_LAMBDA_D
    lambda_a := V.table W_LAMBDA_A
    dbl_diff := V.table W_TEMP4
    add_diff := V.table W_TEMP5 }

-- ============================================================
-- Section 10: Full inductive extraction (statement)
-- ============================================================

/-- **Scalar multiplication gate extraction** (statement):

    Given `n` scalar multiplication steps (6n layers total), if:
    - All layers are consistent (each gate constraint is satisfied)
    - The zero wire is zero at the bottom layer
    - The prover-supplied temporary wires satisfy the correct difference relationships

    Then the `ecScalarMulChain` predicate holds.

    This is the hardest theorem in the gate-level ECDSA circuit verification,
    requiring induction over `n` steps with careful bookkeeping of how
    wire values at step boundaries align with `ecScalarMulChain`'s
    `intermediates`, `doubled`, `scalar_bits`, etc.

    The 6 multiplication equations per step (proved above) are necessary
    but not sufficient: we also need the prover's auxiliary wire values
    to correctly encode the differences `x_1 - x_3` and `x_2 - x_1`,
    and the accumulator/doubled point coordinates to propagate correctly
    between steps. -/
theorem scalar_mul_gate_extraction
    (params : CurveParams F) (n : ℕ)
    (values : Fin (6 * n + 1) → LayerValues F 5)
    -- All layers are consistent
    (hcons : ∀ (k : Fin (6 * n)),
      ∀ g, layerConsistent
        (scalarMulAllLayers F n ⟨k.val, k.isLt⟩)
        (values ⟨k.val, by omega⟩)
        (values ⟨k.val + 1, by omega⟩)
        g)
    -- Zero wire is zero at the bottom
    (hzero : (values ⟨6 * n, by omega⟩).table W_ZERO = 0)
    -- Prover supplies correct difference wires at each step boundary:
    -- At step i, the bottom layer (values at 6*(i+1)) has:
    --   W_TEMP4 = acc_x - dbl_x (for doubling y₃ check)
    --   W_TEMP5 = px - dbl_x (for addition slope check)
    (hdiffs : ∀ (i : Fin n),
      let V := values ⟨6 * (i.val + 1), by omega⟩
      V.table W_TEMP4 = V.table W_ACC_X - V.table W_DBL_X ∧
      V.table W_TEMP5 = V.table W_PX - V.table W_DBL_X) :
    ∃ (scalar_bits : Fin n → F) (intermediates : Fin (n + 1) → ECPoint F)
      (doubled : Fin n → ECPoint F)
      (double_lambdas add_lambdas : Fin n → F),
    -- The scalar bits are read from the wire
    (∀ i : Fin n, scalar_bits i =
      (values ⟨6 * (i.val + 1), by omega⟩).table W_BIT) ∧
    -- The chain constraint holds
    ecScalarMulChain params n scalar_bits
      ⟨(values ⟨6 * n, by omega⟩).table W_PX,
       (values ⟨6 * n, by omega⟩).table W_PY, 0⟩
      intermediates doubled double_lambdas add_lambdas := by
  sorry

-- ============================================================
-- Section 11: Per-step accumulator propagation
-- ============================================================

/-- Key wires pass through all 6 layers of a step unchanged. -/
theorem smStep_acc_passthrough
    (values : Fin 7 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (hzero6 : (values 6).table W_ZERO = 0) :
    -- W_ACC_X propagates from layer 0 to layer 6
    (values 0).table W_ACC_X = (values 6).table W_ACC_X ∧
    -- W_ACC_Y propagates from layer 0 to layer 6
    (values 0).table W_ACC_Y = (values 6).table W_ACC_Y ∧
    -- W_LAMBDA_D propagates from layer 0 to layer 6
    (values 0).table W_LAMBDA_D = (values 6).table W_LAMBDA_D ∧
    -- W_LAMBDA_A propagates from layer 0 to layer 6
    (values 0).table W_LAMBDA_A = (values 6).table W_LAMBDA_A := by
  have ⟨hz5, hz4, hz3, hz2, hz1, hz0⟩ :=
    smStep_zero_wire_chain F values hcons0 hcons1 hcons2 hcons3 hcons4 hcons5 hzero6
  -- Extract passthrough equations
  have hpass0 := ((smLayer0_iff F (values 0) (values 1)).mp hcons0).2.1
  have hpass1 := ((smLayer1_iff F (values 1) (values 2)).mp hcons1).2.1
  have hpass2 := ((smLayer2_iff F (values 2) (values 3)).mp hcons2).2.1
  have hpass3 := ((smLayer3_iff F (values 3) (values 4)).mp hcons3).2.1
  have hpass4 := ((smLayer4_iff F (values 4) (values 5)).mp hcons4).2.1
  have hpass5 := ((smLayer5_iff F (values 5) (values 6)).mp hcons5).2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- W_ACC_X: passes through all 6 layers
    calc (values 0).table W_ACC_X
        = (values 1).table W_ACC_X := passthrough_exact (hpass0 W_ACC_X W_ACC_X_in_smL0) hz1
      _ = (values 2).table W_ACC_X := passthrough_exact (hpass1 W_ACC_X W_ACC_X_in_smL1) hz2
      _ = (values 3).table W_ACC_X := passthrough_exact (hpass2 W_ACC_X W_ACC_X_in_smL2) hz3
      _ = (values 4).table W_ACC_X := passthrough_exact (hpass3 W_ACC_X W_ACC_X_in_smL3) hz4
      _ = (values 5).table W_ACC_X := passthrough_exact (hpass4 W_ACC_X W_ACC_X_in_smL4) hz5
      _ = (values 6).table W_ACC_X := passthrough_exact (hpass5 W_ACC_X W_ACC_X_in_smL5) hzero6
  · -- W_ACC_Y: passes through all 6 layers
    calc (values 0).table W_ACC_Y
        = (values 1).table W_ACC_Y := passthrough_exact (hpass0 W_ACC_Y W_ACC_Y_in_smL0) hz1
      _ = (values 2).table W_ACC_Y := passthrough_exact (hpass1 W_ACC_Y W_ACC_Y_in_smL1) hz2
      _ = (values 3).table W_ACC_Y := passthrough_exact (hpass2 W_ACC_Y W_ACC_Y_in_smL2) hz3
      _ = (values 4).table W_ACC_Y := passthrough_exact (hpass3 W_ACC_Y W_ACC_Y_in_smL3) hz4
      _ = (values 5).table W_ACC_Y := passthrough_exact (hpass4 W_ACC_Y W_ACC_Y_in_smL4) hz5
      _ = (values 6).table W_ACC_Y := passthrough_exact (hpass5 W_ACC_Y W_ACC_Y_in_smL5) hzero6
  · -- W_LAMBDA_D: passes through all 6 layers
    calc (values 0).table W_LAMBDA_D
        = (values 1).table W_LAMBDA_D := passthrough_exact (hpass0 W_LAMBDA_D W_LAMBDA_D_in_smL0) hz1
      _ = (values 2).table W_LAMBDA_D := passthrough_exact (hpass1 W_LAMBDA_D (by native_decide)) hz2
      _ = (values 3).table W_LAMBDA_D := passthrough_exact (hpass2 W_LAMBDA_D (by native_decide)) hz3
      _ = (values 4).table W_LAMBDA_D := passthrough_exact (hpass3 W_LAMBDA_D W_LAMBDA_D_in_smL3) hz4
      _ = (values 5).table W_LAMBDA_D := passthrough_exact (hpass4 W_LAMBDA_D W_LAMBDA_D_in_smL4) hz5
      _ = (values 6).table W_LAMBDA_D := passthrough_exact (hpass5 W_LAMBDA_D W_LAMBDA_D_in_smL5) hzero6
  · -- W_LAMBDA_A: passes through all 6 layers
    calc (values 0).table W_LAMBDA_A
        = (values 1).table W_LAMBDA_A := passthrough_exact (hpass0 W_LAMBDA_A W_LAMBDA_A_in_smL0) hz1
      _ = (values 2).table W_LAMBDA_A := passthrough_exact (hpass1 W_LAMBDA_A W_LAMBDA_A_in_smL1) hz2
      _ = (values 3).table W_LAMBDA_A := passthrough_exact (hpass2 W_LAMBDA_A W_LAMBDA_A_in_smL2) hz3
      _ = (values 4).table W_LAMBDA_A := passthrough_exact (hpass3 W_LAMBDA_A (by native_decide)) hz4
      _ = (values 5).table W_LAMBDA_A := passthrough_exact (hpass4 W_LAMBDA_A (by native_decide)) hz5
      _ = (values 6).table W_LAMBDA_A := passthrough_exact (hpass5 W_LAMBDA_A (by native_decide)) hzero6
