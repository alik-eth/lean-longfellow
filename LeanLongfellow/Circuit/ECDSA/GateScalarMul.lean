import LeanLongfellow.Circuit.GateCircuit
import LeanLongfellow.Circuit.ECArith

open Finset MultilinearPoly

set_option autoImplicit false

/-! # ECDSA Gate-Level Scalar Multiplication (Phase B)

Seven `mulPassLayer` layers per scalar multiplication step, verifying the
multiplication constraints arising from point doubling, conditional addition,
and scalar bit boolean enforcement.

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
- **Boolean enforcement** (`isBool`): 1 multiplication
  7. `bit * bit -> zcheck` (computes `bit^2`; combined with a zero-check
     hypothesis `zcheck = bit` at step boundaries, this forces `bit^2 = bit`,
     i.e., `isBool bit`)

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
W_ZCHECK (30)                                -- bit^2 for isBool check
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

/-- Passthroughs for layer 6 (boolean check: bit * bit -> zcheck).
    All non-zero wires except W_ZCHECK. -/
def smLayer6Pass : List (Fin 5 → Bool) :=
  [W_SINV, W_U1, W_U2, W_ACC_X, W_ACC_Y, W_ACC_INF, W_DBL_X, W_DBL_Y, W_DBL_INF,
   W_PX, W_PY, W_BIT, W_LAMBDA_D, W_LAMBDA_A, W_TEMP1, W_TEMP2, W_TEMP3,
   W_P1_X, W_P1_Y, W_P1_INF, W_P2_X, W_P2_Y, W_P2_INF,
   W_FINAL_X, W_FINAL_Y, W_FINAL_INF, W_FINAL_LAM, W_TEMP4, W_TEMP5, W_OUTPUT]

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

/-- Layer 6: Boolean enforcement -- `bit * bit -> zcheck`.
    Computes `bit^2`; combined with a zero-check at step boundaries
    (`zcheck = bit`), this forces `bit^2 = bit`, i.e., `isBool bit`. -/
def smLayer6 : CircuitLayer F 5 :=
  mulPassLayer F W_ZCHECK W_BIT W_BIT smLayer6Pass

-- ============================================================
-- Section 3: The 7-layer step bundle
-- ============================================================

/-- The 7 layers for one scalar multiplication step (doubling + conditional add + isBool). -/
def scalarMulStepLayers : Fin 7 → CircuitLayer F 5
  | ⟨0, _⟩ => smLayer0 F
  | ⟨1, _⟩ => smLayer1 F
  | ⟨2, _⟩ => smLayer2 F
  | ⟨3, _⟩ => smLayer3 F
  | ⟨4, _⟩ => smLayer4 F
  | ⟨5, _⟩ => smLayer5 F
  | ⟨6, _⟩ => smLayer6 F

/-- All layers for `n` scalar multiplication steps: `7*n` layers total.
    Step `k` uses layers `7*k` through `7*k+6`. -/
def scalarMulAllLayers (n : ℕ) : Fin (7 * n) → CircuitLayer F 5 :=
  fun ⟨i, hi⟩ =>
    scalarMulStepLayers F ⟨i % 7, Nat.mod_lt i (by omega)⟩

-- ============================================================
-- Section 4: Distinctness and precondition lemmas
-- ============================================================

-- Wire distinctness for output positions
private theorem W_TEMP1_ne_ZERO' : W_TEMP1 ≠ W_ZERO := by native_decide
private theorem W_TEMP2_ne_ZERO : W_TEMP2 ≠ W_ZERO := by native_decide
private theorem W_TEMP3_ne_ZERO : W_TEMP3 ≠ W_ZERO := by native_decide
private theorem W_ZCHECK_ne_ZERO : W_ZCHECK ≠ W_ZERO := by native_decide

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

-- Layer 6 preconditions
private theorem smL6_pass_ne_zero : ∀ p ∈ smLayer6Pass, p ≠ W_ZERO := by native_decide
private theorem smL6_pass_ne_out : ∀ p ∈ smLayer6Pass, p ≠ W_ZCHECK := by native_decide
private theorem smL6_pass_nodup : smLayer6Pass.Nodup := by native_decide

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

/-- Layer 6 semantics: `V_curr(W_ZCHECK) = V_next(W_BIT) * V_next(W_BIT)`. -/
theorem smLayer6_iff (V_curr V_next : LayerValues F 5) :
    (∀ g, layerConsistent (smLayer6 F) V_curr V_next g) ↔
    (V_curr.table W_ZCHECK = V_next.table W_BIT * V_next.table W_BIT ∧
     (∀ p ∈ smLayer6Pass, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ W_ZCHECK → q ∉ smLayer6Pass → q ≠ W_ZERO → V_curr.table q = 0)) :=
  mulPassLayer_iff F W_ZCHECK W_BIT W_BIT smLayer6Pass V_curr V_next
    W_ZCHECK_ne_ZERO smL6_pass_ne_zero smL6_pass_ne_out smL6_pass_nodup

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
-- W_ACC_X passes through layer 6
private theorem W_ACC_X_in_smL6 : W_ACC_X ∈ smLayer6Pass := by native_decide

-- W_LAMBDA_D passes through layer 6
private theorem W_LAMBDA_D_in_smL6 : W_LAMBDA_D ∈ smLayer6Pass := by native_decide

-- W_LAMBDA_A passes through layer 6
private theorem W_LAMBDA_A_in_smL6 : W_LAMBDA_A ∈ smLayer6Pass := by native_decide

-- W_TEMP4 passes through layer 6
private theorem W_TEMP4_in_smL6 : W_TEMP4 ∈ smLayer6Pass := by native_decide

-- W_TEMP5 passes through layer 6
private theorem W_TEMP5_in_smL6 : W_TEMP5 ∈ smLayer6Pass := by native_decide

-- W_ACC_Y passes through layer 6
private theorem W_ACC_Y_in_smL6 : W_ACC_Y ∈ smLayer6Pass := by native_decide

-- W_BIT passes through layers 0-5
private theorem W_BIT_in_smL0 : W_BIT ∈ smLayer0Pass := by native_decide
private theorem W_BIT_in_smL1 : W_BIT ∈ smLayer1Pass := by native_decide
private theorem W_BIT_in_smL2 : W_BIT ∈ smLayer2Pass := by native_decide
private theorem W_BIT_in_smL3 : W_BIT ∈ smLayer3Pass := by native_decide
private theorem W_BIT_in_smL4 : W_BIT ∈ smLayer4Pass := by native_decide
private theorem W_BIT_in_smL5 : W_BIT ∈ smLayer5Pass := by native_decide
-- W_BIT is consumed by layer 6 (as input), passes through layer 6's passthrough list
private theorem W_BIT_in_smL6 : W_BIT ∈ smLayer6Pass := by native_decide

-- W_ZCHECK passes through layers 0-5 (consumed by layer 6 as output)
private theorem W_ZCHECK_in_smL0 : W_ZCHECK ∈ smLayer0Pass := by native_decide
private theorem W_ZCHECK_in_smL1 : W_ZCHECK ∈ smLayer1Pass := by native_decide
private theorem W_ZCHECK_in_smL2 : W_ZCHECK ∈ smLayer2Pass := by native_decide
private theorem W_ZCHECK_in_smL3 : W_ZCHECK ∈ smLayer3Pass := by native_decide
private theorem W_ZCHECK_in_smL4 : W_ZCHECK ∈ smLayer4Pass := by native_decide
private theorem W_ZCHECK_in_smL5 : W_ZCHECK ∈ smLayer5Pass := by native_decide

-- ============================================================
-- Section 7: Zero wire propagation
-- ============================================================

/-- Zero wire is zero at every layer boundary of a consistent scalar mul step. -/
theorem smStep_zero_wire_chain
    (values : Fin 8 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (hcons6 : ∀ g, layerConsistent (smLayer6 F) (values 6) (values 7) g)
    (_hzero7 : (values 7).table W_ZERO = 0) :
    (values 6).table W_ZERO = 0 ∧
    (values 5).table W_ZERO = 0 ∧
    (values 4).table W_ZERO = 0 ∧
    (values 3).table W_ZERO = 0 ∧
    (values 2).table W_ZERO = 0 ∧
    (values 1).table W_ZERO = 0 ∧
    (values 0).table W_ZERO = 0 := by
  have hz6 := ((smLayer6_iff F (values 6) (values 7)).mp hcons6).2.2.1
  have hz5 := ((smLayer5_iff F (values 5) (values 6)).mp hcons5).2.2.1
  have hz4 := ((smLayer4_iff F (values 4) (values 5)).mp hcons4).2.2.1
  have hz3 := ((smLayer3_iff F (values 3) (values 4)).mp hcons3).2.2.1
  have hz2 := ((smLayer2_iff F (values 2) (values 3)).mp hcons2).2.2.1
  have hz1 := ((smLayer1_iff F (values 1) (values 2)).mp hcons1).2.2.1
  have hz0 := ((smLayer0_iff F (values 0) (values 1)).mp hcons0).2.2.1
  exact ⟨hz6, hz5, hz4, hz3, hz2, hz1, hz0⟩

-- ============================================================
-- Section 8: One-step multiplication equations extraction
-- ============================================================

/-- **Scalar mul step extraction**: from layer consistency of the 7 layers
    in one scalar multiplication step, extract the 7 multiplication equations.

    The wires carrying `lambda_d`, `lambda_a`, `acc_x`, `temp4`, `temp5`, `bit`
    are traced back through passthrough gates to the bottom layer (values 7), yielding:

    1. `V_0(W_TEMP1) = V_7(W_ACC_X)^2`
    2. `V_1(W_TEMP2) = V_7(W_LAMBDA_D)^2`
    3. `V_2(W_TEMP3) = V_7(W_LAMBDA_D) * V_7(W_TEMP4)`
    4. `V_3(W_TEMP1) = V_7(W_LAMBDA_A) * V_7(W_TEMP5)`
    5. `V_4(W_TEMP2) = V_7(W_LAMBDA_A)^2`
    6. `V_5(W_TEMP3) = V_7(W_LAMBDA_A) * V_7(W_ACC_X)`
    7. `V_6(W_ZCHECK) = V_7(W_BIT)^2` -/
theorem scalarMul_step_mul_equations
    (values : Fin 8 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (hcons6 : ∀ g, layerConsistent (smLayer6 F) (values 6) (values 7) g)
    (hzero7 : (values 7).table W_ZERO = 0) :
    -- Doubling multiplications
    (values 0).table W_TEMP1 = (values 7).table W_ACC_X * (values 7).table W_ACC_X ∧
    (values 1).table W_TEMP2 = (values 7).table W_LAMBDA_D * (values 7).table W_LAMBDA_D ∧
    (values 2).table W_TEMP3 = (values 7).table W_LAMBDA_D * (values 7).table W_TEMP4 ∧
    -- Addition multiplications
    (values 3).table W_TEMP1 = (values 7).table W_LAMBDA_A * (values 7).table W_TEMP5 ∧
    (values 4).table W_TEMP2 = (values 7).table W_LAMBDA_A * (values 7).table W_LAMBDA_A ∧
    (values 5).table W_TEMP3 = (values 7).table W_LAMBDA_A * (values 7).table W_ACC_X ∧
    -- Boolean enforcement
    (values 6).table W_ZCHECK = (values 7).table W_BIT * (values 7).table W_BIT := by
  -- Extract per-layer semantics
  have h0 := (smLayer0_iff F (values 0) (values 1)).mp hcons0
  have h1 := (smLayer1_iff F (values 1) (values 2)).mp hcons1
  have h2 := (smLayer2_iff F (values 2) (values 3)).mp hcons2
  have h3 := (smLayer3_iff F (values 3) (values 4)).mp hcons3
  have h4 := (smLayer4_iff F (values 4) (values 5)).mp hcons4
  have h5 := (smLayer5_iff F (values 5) (values 6)).mp hcons5
  have h6 := (smLayer6_iff F (values 6) (values 7)).mp hcons6
  -- Extract zero-wire facts
  have ⟨hz6, hz5, hz4, hz3, hz2, hz1, _⟩ :=
    smStep_zero_wire_chain F values hcons0 hcons1 hcons2 hcons3 hcons4 hcons5 hcons6 hzero7
  -- Extract mul equations and passthrough equations
  obtain ⟨hmul0, hpass0, _, _⟩ := h0
  obtain ⟨hmul1, hpass1, _, _⟩ := h1
  obtain ⟨hmul2, hpass2, _, _⟩ := h2
  obtain ⟨hmul3, hpass3, _, _⟩ := h3
  obtain ⟨hmul4, hpass4, _, _⟩ := h4
  obtain ⟨hmul5, hpass5, _, _⟩ := h5
  obtain ⟨hmul6, hpass6, _, _⟩ := h6
  -- Trace W_ACC_X from layer 1 back to layer 7
  have haccx_12 : (values 1).table W_ACC_X = (values 2).table W_ACC_X :=
    passthrough_exact (hpass1 W_ACC_X W_ACC_X_in_smL1) hz2
  have haccx_23 : (values 2).table W_ACC_X = (values 3).table W_ACC_X :=
    passthrough_exact (hpass2 W_ACC_X W_ACC_X_in_smL2) hz3
  have haccx_34 : (values 3).table W_ACC_X = (values 4).table W_ACC_X :=
    passthrough_exact (hpass3 W_ACC_X W_ACC_X_in_smL3) hz4
  have haccx_45 : (values 4).table W_ACC_X = (values 5).table W_ACC_X :=
    passthrough_exact (hpass4 W_ACC_X W_ACC_X_in_smL4) hz5
  have haccx_56 : (values 5).table W_ACC_X = (values 6).table W_ACC_X :=
    passthrough_exact (hpass5 W_ACC_X W_ACC_X_in_smL5) hz6
  have haccx_67 : (values 6).table W_ACC_X = (values 7).table W_ACC_X :=
    passthrough_exact (hpass6 W_ACC_X W_ACC_X_in_smL6) hzero7
  -- Trace W_LAMBDA_D from layer 1 back to layer 7
  have hld_12 : (values 1).table W_LAMBDA_D = (values 2).table W_LAMBDA_D :=
    passthrough_exact (hpass1 W_LAMBDA_D (by native_decide)) hz2
  have hld_23 : (values 2).table W_LAMBDA_D = (values 3).table W_LAMBDA_D :=
    passthrough_exact (hpass2 W_LAMBDA_D (by native_decide)) hz3
  have hld_34 : (values 3).table W_LAMBDA_D = (values 4).table W_LAMBDA_D :=
    passthrough_exact (hpass3 W_LAMBDA_D W_LAMBDA_D_in_smL3) hz4
  have hld_45 : (values 4).table W_LAMBDA_D = (values 5).table W_LAMBDA_D :=
    passthrough_exact (hpass4 W_LAMBDA_D W_LAMBDA_D_in_smL4) hz5
  have hld_56 : (values 5).table W_LAMBDA_D = (values 6).table W_LAMBDA_D :=
    passthrough_exact (hpass5 W_LAMBDA_D W_LAMBDA_D_in_smL5) hz6
  have hld_67 : (values 6).table W_LAMBDA_D = (values 7).table W_LAMBDA_D :=
    passthrough_exact (hpass6 W_LAMBDA_D W_LAMBDA_D_in_smL6) hzero7
  -- Trace W_TEMP4 from layer 1 back to layer 7
  have ht4_12 : (values 1).table W_TEMP4 = (values 2).table W_TEMP4 :=
    passthrough_exact (hpass1 W_TEMP4 W_TEMP4_in_smL1) hz2
  have ht4_23 : (values 2).table W_TEMP4 = (values 3).table W_TEMP4 :=
    passthrough_exact (hpass2 W_TEMP4 (by native_decide)) hz3
  have ht4_34 : (values 3).table W_TEMP4 = (values 4).table W_TEMP4 :=
    passthrough_exact (hpass3 W_TEMP4 W_TEMP4_in_smL3) hz4
  have ht4_45 : (values 4).table W_TEMP4 = (values 5).table W_TEMP4 :=
    passthrough_exact (hpass4 W_TEMP4 W_TEMP4_in_smL4) hz5
  have ht4_56 : (values 5).table W_TEMP4 = (values 6).table W_TEMP4 :=
    passthrough_exact (hpass5 W_TEMP4 W_TEMP4_in_smL5) hz6
  have ht4_67 : (values 6).table W_TEMP4 = (values 7).table W_TEMP4 :=
    passthrough_exact (hpass6 W_TEMP4 W_TEMP4_in_smL6) hzero7
  -- Trace W_LAMBDA_A from layer 1 back to layer 7
  have hla_12 : (values 1).table W_LAMBDA_A = (values 2).table W_LAMBDA_A :=
    passthrough_exact (hpass1 W_LAMBDA_A W_LAMBDA_A_in_smL1) hz2
  have hla_23 : (values 2).table W_LAMBDA_A = (values 3).table W_LAMBDA_A :=
    passthrough_exact (hpass2 W_LAMBDA_A W_LAMBDA_A_in_smL2) hz3
  have hla_34 : (values 3).table W_LAMBDA_A = (values 4).table W_LAMBDA_A :=
    passthrough_exact (hpass3 W_LAMBDA_A (by native_decide)) hz4
  have hla_45 : (values 4).table W_LAMBDA_A = (values 5).table W_LAMBDA_A :=
    passthrough_exact (hpass4 W_LAMBDA_A (by native_decide)) hz5
  have hla_56 : (values 5).table W_LAMBDA_A = (values 6).table W_LAMBDA_A :=
    passthrough_exact (hpass5 W_LAMBDA_A (by native_decide)) hz6
  have hla_67 : (values 6).table W_LAMBDA_A = (values 7).table W_LAMBDA_A :=
    passthrough_exact (hpass6 W_LAMBDA_A W_LAMBDA_A_in_smL6) hzero7
  -- Trace W_TEMP5 from layer 1 back to layer 7
  have ht5_12 : (values 1).table W_TEMP5 = (values 2).table W_TEMP5 :=
    passthrough_exact (hpass1 W_TEMP5 W_TEMP5_in_smL1) hz2
  have ht5_23 : (values 2).table W_TEMP5 = (values 3).table W_TEMP5 :=
    passthrough_exact (hpass2 W_TEMP5 W_TEMP5_in_smL2) hz3
  have ht5_34 : (values 3).table W_TEMP5 = (values 4).table W_TEMP5 :=
    passthrough_exact (hpass3 W_TEMP5 (by native_decide)) hz4
  have ht5_45 : (values 4).table W_TEMP5 = (values 5).table W_TEMP5 :=
    passthrough_exact (hpass4 W_TEMP5 W_TEMP5_in_smL4) hz5
  have ht5_56 : (values 5).table W_TEMP5 = (values 6).table W_TEMP5 :=
    passthrough_exact (hpass5 W_TEMP5 W_TEMP5_in_smL5) hz6
  have ht5_67 : (values 6).table W_TEMP5 = (values 7).table W_TEMP5 :=
    passthrough_exact (hpass6 W_TEMP5 W_TEMP5_in_smL6) hzero7
  -- Assemble all 7 equations
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Equation 1: V_0(W_TEMP1) = V_7(W_ACC_X)^2
    rw [hmul0]
    -- V_1(W_ACC_X) = V_7(W_ACC_X) by tracing through layers 1-7
    rw [haccx_12, haccx_23, haccx_34, haccx_45, haccx_56, haccx_67]
  · -- Equation 2: V_1(W_TEMP2) = V_7(W_LAMBDA_D)^2
    rw [hmul1]
    rw [hld_23, hld_34, hld_45, hld_56, hld_67]
  · -- Equation 3: V_2(W_TEMP3) = V_7(W_LAMBDA_D) * V_7(W_TEMP4)
    rw [hmul2]
    rw [hld_34, hld_45, hld_56, hld_67]
    rw [ht4_34, ht4_45, ht4_56, ht4_67]
  · -- Equation 4: V_3(W_TEMP1) = V_7(W_LAMBDA_A) * V_7(W_TEMP5)
    rw [hmul3]
    rw [hla_45, hla_56, hla_67]
    rw [ht5_45, ht5_56, ht5_67]
  · -- Equation 5: V_4(W_TEMP2) = V_7(W_LAMBDA_A)^2
    rw [hmul4]
    rw [hla_56, hla_67]
  · -- Equation 6: V_5(W_TEMP3) = V_7(W_LAMBDA_A) * V_7(W_ACC_X)
    rw [hmul5]
    rw [hla_67]
    rw [haccx_67]
  · -- Equation 7: V_6(W_ZCHECK) = V_7(W_BIT)^2
    exact hmul6

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
-- Section 10: Per-step accumulator propagation
-- ============================================================

/-- Key wires pass through all 7 layers of a step unchanged. -/
theorem smStep_acc_passthrough
    (values : Fin 8 → LayerValues F 5)
    (hcons0 : ∀ g, layerConsistent (smLayer0 F) (values 0) (values 1) g)
    (hcons1 : ∀ g, layerConsistent (smLayer1 F) (values 1) (values 2) g)
    (hcons2 : ∀ g, layerConsistent (smLayer2 F) (values 2) (values 3) g)
    (hcons3 : ∀ g, layerConsistent (smLayer3 F) (values 3) (values 4) g)
    (hcons4 : ∀ g, layerConsistent (smLayer4 F) (values 4) (values 5) g)
    (hcons5 : ∀ g, layerConsistent (smLayer5 F) (values 5) (values 6) g)
    (hcons6 : ∀ g, layerConsistent (smLayer6 F) (values 6) (values 7) g)
    (hzero7 : (values 7).table W_ZERO = 0) :
    -- W_ACC_X propagates from layer 0 to layer 7
    (values 0).table W_ACC_X = (values 7).table W_ACC_X ∧
    -- W_ACC_Y propagates from layer 0 to layer 7
    (values 0).table W_ACC_Y = (values 7).table W_ACC_Y ∧
    -- W_LAMBDA_D propagates from layer 0 to layer 7
    (values 0).table W_LAMBDA_D = (values 7).table W_LAMBDA_D ∧
    -- W_LAMBDA_A propagates from layer 0 to layer 7
    (values 0).table W_LAMBDA_A = (values 7).table W_LAMBDA_A ∧
    -- W_BIT propagates from layer 0 to layer 7
    (values 0).table W_BIT = (values 7).table W_BIT := by
  have ⟨hz6, hz5, hz4, hz3, hz2, hz1, hz0⟩ :=
    smStep_zero_wire_chain F values hcons0 hcons1 hcons2 hcons3 hcons4 hcons5 hcons6 hzero7
  -- Extract passthrough equations
  have hpass0 := ((smLayer0_iff F (values 0) (values 1)).mp hcons0).2.1
  have hpass1 := ((smLayer1_iff F (values 1) (values 2)).mp hcons1).2.1
  have hpass2 := ((smLayer2_iff F (values 2) (values 3)).mp hcons2).2.1
  have hpass3 := ((smLayer3_iff F (values 3) (values 4)).mp hcons3).2.1
  have hpass4 := ((smLayer4_iff F (values 4) (values 5)).mp hcons4).2.1
  have hpass5 := ((smLayer5_iff F (values 5) (values 6)).mp hcons5).2.1
  have hpass6 := ((smLayer6_iff F (values 6) (values 7)).mp hcons6).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- W_ACC_X: passes through all 7 layers
    calc (values 0).table W_ACC_X
        = (values 1).table W_ACC_X := passthrough_exact (hpass0 W_ACC_X W_ACC_X_in_smL0) hz1
      _ = (values 2).table W_ACC_X := passthrough_exact (hpass1 W_ACC_X W_ACC_X_in_smL1) hz2
      _ = (values 3).table W_ACC_X := passthrough_exact (hpass2 W_ACC_X W_ACC_X_in_smL2) hz3
      _ = (values 4).table W_ACC_X := passthrough_exact (hpass3 W_ACC_X W_ACC_X_in_smL3) hz4
      _ = (values 5).table W_ACC_X := passthrough_exact (hpass4 W_ACC_X W_ACC_X_in_smL4) hz5
      _ = (values 6).table W_ACC_X := passthrough_exact (hpass5 W_ACC_X W_ACC_X_in_smL5) hz6
      _ = (values 7).table W_ACC_X := passthrough_exact (hpass6 W_ACC_X W_ACC_X_in_smL6) hzero7
  · -- W_ACC_Y: passes through all 7 layers
    calc (values 0).table W_ACC_Y
        = (values 1).table W_ACC_Y := passthrough_exact (hpass0 W_ACC_Y W_ACC_Y_in_smL0) hz1
      _ = (values 2).table W_ACC_Y := passthrough_exact (hpass1 W_ACC_Y W_ACC_Y_in_smL1) hz2
      _ = (values 3).table W_ACC_Y := passthrough_exact (hpass2 W_ACC_Y W_ACC_Y_in_smL2) hz3
      _ = (values 4).table W_ACC_Y := passthrough_exact (hpass3 W_ACC_Y W_ACC_Y_in_smL3) hz4
      _ = (values 5).table W_ACC_Y := passthrough_exact (hpass4 W_ACC_Y W_ACC_Y_in_smL4) hz5
      _ = (values 6).table W_ACC_Y := passthrough_exact (hpass5 W_ACC_Y W_ACC_Y_in_smL5) hz6
      _ = (values 7).table W_ACC_Y := passthrough_exact (hpass6 W_ACC_Y W_ACC_Y_in_smL6) hzero7
  · -- W_LAMBDA_D: passes through all 7 layers
    calc (values 0).table W_LAMBDA_D
        = (values 1).table W_LAMBDA_D := passthrough_exact (hpass0 W_LAMBDA_D W_LAMBDA_D_in_smL0) hz1
      _ = (values 2).table W_LAMBDA_D := passthrough_exact (hpass1 W_LAMBDA_D (by native_decide)) hz2
      _ = (values 3).table W_LAMBDA_D := passthrough_exact (hpass2 W_LAMBDA_D (by native_decide)) hz3
      _ = (values 4).table W_LAMBDA_D := passthrough_exact (hpass3 W_LAMBDA_D W_LAMBDA_D_in_smL3) hz4
      _ = (values 5).table W_LAMBDA_D := passthrough_exact (hpass4 W_LAMBDA_D W_LAMBDA_D_in_smL4) hz5
      _ = (values 6).table W_LAMBDA_D := passthrough_exact (hpass5 W_LAMBDA_D W_LAMBDA_D_in_smL5) hz6
      _ = (values 7).table W_LAMBDA_D := passthrough_exact (hpass6 W_LAMBDA_D W_LAMBDA_D_in_smL6) hzero7
  · -- W_LAMBDA_A: passes through all 7 layers
    calc (values 0).table W_LAMBDA_A
        = (values 1).table W_LAMBDA_A := passthrough_exact (hpass0 W_LAMBDA_A W_LAMBDA_A_in_smL0) hz1
      _ = (values 2).table W_LAMBDA_A := passthrough_exact (hpass1 W_LAMBDA_A W_LAMBDA_A_in_smL1) hz2
      _ = (values 3).table W_LAMBDA_A := passthrough_exact (hpass2 W_LAMBDA_A W_LAMBDA_A_in_smL2) hz3
      _ = (values 4).table W_LAMBDA_A := passthrough_exact (hpass3 W_LAMBDA_A (by native_decide)) hz4
      _ = (values 5).table W_LAMBDA_A := passthrough_exact (hpass4 W_LAMBDA_A (by native_decide)) hz5
      _ = (values 6).table W_LAMBDA_A := passthrough_exact (hpass5 W_LAMBDA_A (by native_decide)) hz6
      _ = (values 7).table W_LAMBDA_A := passthrough_exact (hpass6 W_LAMBDA_A W_LAMBDA_A_in_smL6) hzero7
  · -- W_BIT: passes through all 7 layers
    calc (values 0).table W_BIT
        = (values 1).table W_BIT := passthrough_exact (hpass0 W_BIT W_BIT_in_smL0) hz1
      _ = (values 2).table W_BIT := passthrough_exact (hpass1 W_BIT W_BIT_in_smL1) hz2
      _ = (values 3).table W_BIT := passthrough_exact (hpass2 W_BIT W_BIT_in_smL2) hz3
      _ = (values 4).table W_BIT := passthrough_exact (hpass3 W_BIT W_BIT_in_smL3) hz4
      _ = (values 5).table W_BIT := passthrough_exact (hpass4 W_BIT W_BIT_in_smL4) hz5
      _ = (values 6).table W_BIT := passthrough_exact (hpass5 W_BIT W_BIT_in_smL5) hz6
      _ = (values 7).table W_BIT := passthrough_exact (hpass6 W_BIT W_BIT_in_smL6) hzero7

-- ============================================================
-- Section 11: Full inductive extraction (statement)
-- ============================================================

/-- In a field, `x * x = x` implies `isBool x` (i.e., `x ∈ {0, 1}`). -/
theorem isBool_of_sq_eq_self {F : Type*} [Field F] {x : F} (h : x * x = x) : isBool x := by
  unfold isBool; linear_combination -h

/-- **Scalar multiplication gate extraction**:

    Given `n` scalar multiplication steps (7n layers total), if all layers are
    consistent, the zero wire is zero at the bottom, and the boolean zero-check
    wire equals the bit wire at each step boundary, then at each step the
    7 multiplication equations hold, key wires propagate unchanged, and each
    scalar bit is boolean.

    The 7 mul equations per step encode:
    - Doubling: `acc_x^2`, `lambda_d^2`, `lambda_d * temp4`
    - Addition: `lambda_a * temp5`, `lambda_a^2`, `lambda_a * acc_x`
    - Boolean: `bit^2` (combined with `zcheck = bit` hypothesis yields `isBool`)

    Combined with the passthrough (acc_x, acc_y, lambda_d, lambda_a, bit are
    constant within each step), these express the multiplication sub-constraints
    of `ecScalarMulChain`. The remaining linear constraints (slope checks,
    coordinate equations) are verified by other circuit phases.

    The proof works by:
    1. Showing `scalarMulAllLayers` at position `7*i+j` equals `smLayer_j`
    2. Propagating the zero wire backwards from the bottom through each step
    3. Applying `scalarMul_step_mul_equations` at each step
    4. Applying `smStep_acc_passthrough` at each step
    5. Deriving `isBool` from `bit^2 = zcheck = bit` -/
theorem scalar_mul_gate_extraction
    (n : ℕ)
    (values : Fin (7 * n + 1) → LayerValues F 5)
    -- All layers are consistent
    (hcons : ∀ (k : Fin (7 * n)),
      ∀ g, layerConsistent
        (scalarMulAllLayers F n ⟨k.val, k.isLt⟩)
        (values ⟨k.val, by omega⟩)
        (values ⟨k.val + 1, by omega⟩)
        g)
    -- Zero wire is zero at the bottom
    (hzero : (values ⟨7 * n, by omega⟩).table W_ZERO = 0)
    -- Boolean zero-check: the zcheck wire equals the bit wire at the top of each
    -- step. The output accumulator layer (verified separately) enforces this
    -- equality. Combined with the gate equation (layer 6 computes zcheck = bit^2)
    -- and passthrough propagation (bit and zcheck propagate to the top), this
    -- forces bit^2 = bit, i.e., isBool bit.
    (hzcheck : ∀ (i : Fin n),
      (values ⟨7 * i.val, by omega⟩).table W_ZCHECK =
      (values ⟨7 * i.val, by omega⟩).table W_BIT) :
    -- (A) Zero wire is zero at every step boundary
    (∀ (i : Fin (n + 1)), (values ⟨7 * i.val, by omega⟩).table W_ZERO = 0) ∧
    -- (B) At each step, the 7 multiplication equations hold
    (∀ (i : Fin n),
      let Vbot := values ⟨7 * (i.val + 1), by omega⟩
      -- Doubling multiplications (expressed at the bottom-layer values)
      (values ⟨7 * i.val, by omega⟩).table W_TEMP1 =
        Vbot.table W_ACC_X * Vbot.table W_ACC_X ∧
      (values ⟨7 * i.val + 1, by omega⟩).table W_TEMP2 =
        Vbot.table W_LAMBDA_D * Vbot.table W_LAMBDA_D ∧
      (values ⟨7 * i.val + 2, by omega⟩).table W_TEMP3 =
        Vbot.table W_LAMBDA_D * Vbot.table W_TEMP4 ∧
      -- Addition multiplications
      (values ⟨7 * i.val + 3, by omega⟩).table W_TEMP1 =
        Vbot.table W_LAMBDA_A * Vbot.table W_TEMP5 ∧
      (values ⟨7 * i.val + 4, by omega⟩).table W_TEMP2 =
        Vbot.table W_LAMBDA_A * Vbot.table W_LAMBDA_A ∧
      (values ⟨7 * i.val + 5, by omega⟩).table W_TEMP3 =
        Vbot.table W_LAMBDA_A * Vbot.table W_ACC_X ∧
      -- Boolean enforcement
      (values ⟨7 * i.val + 6, by omega⟩).table W_ZCHECK =
        Vbot.table W_BIT * Vbot.table W_BIT) ∧
    -- (C) Key wires propagate unchanged within each step
    (∀ (i : Fin n),
      let Vtop := values ⟨7 * i.val, by omega⟩
      let Vbot := values ⟨7 * (i.val + 1), by omega⟩
      Vtop.table W_ACC_X = Vbot.table W_ACC_X ∧
      Vtop.table W_ACC_Y = Vbot.table W_ACC_Y ∧
      Vtop.table W_LAMBDA_D = Vbot.table W_LAMBDA_D ∧
      Vtop.table W_LAMBDA_A = Vbot.table W_LAMBDA_A ∧
      Vtop.table W_BIT = Vbot.table W_BIT) ∧
    -- (D) Each scalar bit is boolean
    (∀ (i : Fin n),
      isBool ((values ⟨7 * (i.val + 1), by omega⟩).table W_BIT)) := by
  -- Step 1: Zero wire is zero at ALL layer boundaries
  have hzero_all : ∀ k (hk : k ≤ 7 * n), (values ⟨k, by omega⟩).table W_ZERO = 0 := by
    intro k hk
    induction h : (7 * n - k) with
    | zero =>
      have hk_eq : k = 7 * n := by omega
      cases hk_eq; exact hzero
    | succ m ih =>
      have hk_lt : k < 7 * n := by omega
      have hj : k % 7 < 7 := Nat.mod_lt k (by omega)
      have hck := hcons ⟨k, hk_lt⟩
      have hlk : scalarMulAllLayers F n ⟨k, hk_lt⟩ = scalarMulStepLayers F ⟨k % 7, hj⟩ := by
        simp only [scalarMulAllLayers]
      rw [hlk] at hck
      revert hck; match k % 7, hj with
      | 0, _ => intro hck; exact ((smLayer0_iff F _ _).mp hck).2.2.1
      | 1, _ => intro hck; exact ((smLayer1_iff F _ _).mp hck).2.2.1
      | 2, _ => intro hck; exact ((smLayer2_iff F _ _).mp hck).2.2.1
      | 3, _ => intro hck; exact ((smLayer3_iff F _ _).mp hck).2.2.1
      | 4, _ => intro hck; exact ((smLayer4_iff F _ _).mp hck).2.2.1
      | 5, _ => intro hck; exact ((smLayer5_iff F _ _).mp hck).2.2.1
      | 6, _ => intro hck; exact ((smLayer6_iff F _ _).mp hck).2.2.1
  -- Step 2: Establish per-step layer facts
  have hlayer : ∀ (i : Fin n) (j : Fin 7),
      scalarMulAllLayers F n ⟨7 * i.val + j.val, by omega⟩ =
      scalarMulStepLayers F j := by
    intro i j; simp only [scalarMulAllLayers]; congr 1; simp only [Fin.ext_iff]; omega
  let sv : Fin n → Fin 8 → LayerValues F 5 :=
    fun i j => values ⟨7 * i.val + j.val, by omega⟩
  have hsl : ∀ (i : Fin n) (j : Fin 7) (g : Fin 5 → Bool),
      layerConsistent (scalarMulStepLayers F j) (sv i ⟨j.val, by omega⟩) (sv i ⟨j.val + 1, by omega⟩) g := by
    intro i j g; have := hcons ⟨7 * i.val + j.val, by omega⟩ g; rwa [hlayer i j] at this
  have hsc0 : ∀ (i : Fin n) g, layerConsistent (smLayer0 F) (sv i 0) (sv i 1) g := by
    intro i g; have := hsl i ⟨0, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc1 : ∀ (i : Fin n) g, layerConsistent (smLayer1 F) (sv i 1) (sv i 2) g := by
    intro i g; have := hsl i ⟨1, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc2 : ∀ (i : Fin n) g, layerConsistent (smLayer2 F) (sv i 2) (sv i 3) g := by
    intro i g; have := hsl i ⟨2, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc3 : ∀ (i : Fin n) g, layerConsistent (smLayer3 F) (sv i 3) (sv i 4) g := by
    intro i g; have := hsl i ⟨3, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc4 : ∀ (i : Fin n) g, layerConsistent (smLayer4 F) (sv i 4) (sv i 5) g := by
    intro i g; have := hsl i ⟨4, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc5 : ∀ (i : Fin n) g, layerConsistent (smLayer5 F) (sv i 5) (sv i 6) g := by
    intro i g; have := hsl i ⟨5, by omega⟩ g; simpa [scalarMulStepLayers]
  have hsc6 : ∀ (i : Fin n) g, layerConsistent (smLayer6 F) (sv i 6) (sv i 7) g := by
    intro i g; have := hsl i ⟨6, by omega⟩ g; simpa [scalarMulStepLayers]
  have hzero_bot : ∀ (i : Fin n), (sv i 7).table W_ZERO = 0 := by
    intro i; exact hzero_all (7 * i.val + 7) (by omega)
  -- Step 3: Assemble the four parts
  refine ⟨fun i => hzero_all (7 * i.val) (by omega), ?_, ?_, ?_⟩
  -- Part (B): mul equations at each step
  · intro i
    exact scalarMul_step_mul_equations F (sv i) (hsc0 i) (hsc1 i) (hsc2 i) (hsc3 i) (hsc4 i) (hsc5 i) (hsc6 i) (hzero_bot i)
  -- Part (C): passthrough at each step
  · intro i
    exact smStep_acc_passthrough F (sv i) (hsc0 i) (hsc1 i) (hsc2 i) (hsc3 i) (hsc4 i) (hsc5 i) (hsc6 i) (hzero_bot i)
  -- Part (D): isBool at each step
  · intro i
    -- From mul equations: V_6(W_ZCHECK) = V_7(W_BIT)^2
    have hmuls := scalarMul_step_mul_equations F (sv i) (hsc0 i) (hsc1 i) (hsc2 i) (hsc3 i) (hsc4 i) (hsc5 i) (hsc6 i) (hzero_bot i)
    have hbit_sq := hmuls.2.2.2.2.2.2
    -- From hzcheck: V_0(W_ZCHECK) = V_0(W_BIT) at the top of the step
    have hzc := hzcheck i
    -- Extract zero-wire and passthrough facts for this step
    have ⟨hz6, hz5, hz4, hz3, hz2, hz1, _⟩ :=
      smStep_zero_wire_chain F (sv i) (hsc0 i) (hsc1 i) (hsc2 i) (hsc3 i) (hsc4 i) (hsc5 i) (hsc6 i) (hzero_bot i)
    have hpass0 := ((smLayer0_iff F (sv i 0) (sv i 1)).mp (hsc0 i)).2.1
    have hpass1 := ((smLayer1_iff F (sv i 1) (sv i 2)).mp (hsc1 i)).2.1
    have hpass2 := ((smLayer2_iff F (sv i 2) (sv i 3)).mp (hsc2 i)).2.1
    have hpass3 := ((smLayer3_iff F (sv i 3) (sv i 4)).mp (hsc3 i)).2.1
    have hpass4 := ((smLayer4_iff F (sv i 4) (sv i 5)).mp (hsc4 i)).2.1
    have hpass5 := ((smLayer5_iff F (sv i 5) (sv i 6)).mp (hsc5 i)).2.1
    have hpass6 := ((smLayer6_iff F (sv i 6) (sv i 7)).mp (hsc6 i)).2.1
    -- Trace W_ZCHECK from layer 0 back to layer 6 (through passthroughs)
    have hzc_01 : (sv i 0).table W_ZCHECK = (sv i 1).table W_ZCHECK :=
      passthrough_exact (hpass0 W_ZCHECK W_ZCHECK_in_smL0) hz1
    have hzc_12 : (sv i 1).table W_ZCHECK = (sv i 2).table W_ZCHECK :=
      passthrough_exact (hpass1 W_ZCHECK W_ZCHECK_in_smL1) hz2
    have hzc_23 : (sv i 2).table W_ZCHECK = (sv i 3).table W_ZCHECK :=
      passthrough_exact (hpass2 W_ZCHECK W_ZCHECK_in_smL2) hz3
    have hzc_34 : (sv i 3).table W_ZCHECK = (sv i 4).table W_ZCHECK :=
      passthrough_exact (hpass3 W_ZCHECK W_ZCHECK_in_smL3) hz4
    have hzc_45 : (sv i 4).table W_ZCHECK = (sv i 5).table W_ZCHECK :=
      passthrough_exact (hpass4 W_ZCHECK W_ZCHECK_in_smL4) hz5
    have hzc_56 : (sv i 5).table W_ZCHECK = (sv i 6).table W_ZCHECK :=
      passthrough_exact (hpass5 W_ZCHECK W_ZCHECK_in_smL5) hz6
    -- So: (sv i 0).W_ZCHECK = (sv i 6).W_ZCHECK = bit^2
    have hzc_top_eq_sq : (sv i 0).table W_ZCHECK = (sv i 7).table W_BIT * (sv i 7).table W_BIT :=
      hzc_01.trans (hzc_12.trans (hzc_23.trans (hzc_34.trans (hzc_45.trans (hzc_56.trans hbit_sq)))))
    -- Trace W_BIT from layer 0 back to layer 7 (through passthroughs)
    have hbit_top : (sv i 0).table W_BIT = (sv i 7).table W_BIT := by
      calc (sv i 0).table W_BIT
          = (sv i 1).table W_BIT := passthrough_exact (hpass0 W_BIT W_BIT_in_smL0) hz1
        _ = (sv i 2).table W_BIT := passthrough_exact (hpass1 W_BIT W_BIT_in_smL1) hz2
        _ = (sv i 3).table W_BIT := passthrough_exact (hpass2 W_BIT W_BIT_in_smL2) hz3
        _ = (sv i 4).table W_BIT := passthrough_exact (hpass3 W_BIT W_BIT_in_smL3) hz4
        _ = (sv i 5).table W_BIT := passthrough_exact (hpass4 W_BIT W_BIT_in_smL4) hz5
        _ = (sv i 6).table W_BIT := passthrough_exact (hpass5 W_BIT W_BIT_in_smL5) hz6
        _ = (sv i 7).table W_BIT := passthrough_exact (hpass6 W_BIT W_BIT_in_smL6) (hzero_bot i)
    -- hzcheck says (values ⟨7*i, _⟩).W_ZCHECK = (values ⟨7*i, _⟩).W_BIT
    -- Convert to sv i 0 (which is values ⟨7*i+0, _⟩ = values ⟨7*i, _⟩)
    have hzc' : (sv i 0).table W_ZCHECK = (sv i 0).table W_BIT := by
      show (values ⟨7 * i.val + 0, _⟩).table W_ZCHECK = (values ⟨7 * i.val + 0, _⟩).table W_BIT
      simp only [Nat.add_zero]; exact hzc
    -- From hzc_top_eq_sq and hbit_top:
    -- (sv i 0).W_ZCHECK = bit^2 and (sv i 0).W_BIT = bit
    -- So bit^2 = bit, hence isBool bit
    rw [hzc_top_eq_sq, hbit_top] at hzc'
    exact isBool_of_sq_eq_self hzc'

