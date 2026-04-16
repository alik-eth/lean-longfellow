import LeanLongfellow.Ligero.ECDSAConstraints
import LeanLongfellow.Circuit.ECDSA.Composition

set_option autoImplicit false

open Finset

/-! # ECDSA Constraint Bridge

Proves that satisfaction of the ECDSA linear + quadratic constraints
implies `ecdsaVerify`. This is the semantic bridge that replaces the
`ecdsaCoefficient` lookup table. -/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Linear constraint extraction lemmas
-- ============================================================

private theorem ecdsaLinear_extract [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig))
    (row : Fin ecdsaLinearCount) :
    ∑ j : Fin ecdsaWitnessSize,
      (ecdsaLinearConstraints F z Q sig).matrix row j * w j =
    (ecdsaLinearConstraints F z Q sig).target row :=
  h row

/-- Extract sig.s assignment from linear constraint satisfaction. -/
theorem ecdsaLinear_sig_s [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig)) :
    w W_SIG_S = sig.s := by
  have h0 := h ⟨0, by unfold ecdsaLinearCount; omega⟩
  unfold satisfiesLinear ecdsaLinearConstraints ecdsaWitnessSize ecdsaLinearCount at h0
  simp only [Fin.sum_univ_eight, Fin.isValue] at h0
  simp only [W_SIG_S]; simp at h0; exact h0

/-- Extract z (message hash) from linear constraint satisfaction. -/
theorem ecdsaLinear_msg_z [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig)) :
    w W_MSG_Z = z := by
  have h1 := h ⟨1, by unfold ecdsaLinearCount; omega⟩
  unfold satisfiesLinear ecdsaLinearConstraints ecdsaWitnessSize ecdsaLinearCount at h1
  simp only [Fin.sum_univ_eight, Fin.isValue] at h1
  simp only [W_MSG_Z]; simp at h1; exact h1

/-- Extract sig.r from linear constraint satisfaction. -/
theorem ecdsaLinear_sig_r [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig)) :
    w W_SIG_R = sig.r := by
  have h2 := h ⟨2, by unfold ecdsaLinearCount; omega⟩
  unfold satisfiesLinear ecdsaLinearConstraints ecdsaWitnessSize ecdsaLinearCount at h2
  simp only [Fin.sum_univ_eight, Fin.isValue] at h2
  simp only [W_SIG_R]; simp at h2; exact h2

/-- Extract s * s_inv = 1 from linear constraint satisfaction. -/
theorem ecdsaLinear_s_product [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig)) :
    w W_S_PRODUCT = 1 := by
  have h3 := h ⟨3, by unfold ecdsaLinearCount; omega⟩
  unfold satisfiesLinear ecdsaLinearConstraints ecdsaWitnessSize ecdsaLinearCount at h3
  simp only [Fin.sum_univ_eight, Fin.isValue] at h3
  simp only [W_S_PRODUCT]; simp at h3; exact h3

/-- Extract xCoord(R) = sig.r from linear constraint satisfaction. -/
theorem ecdsaLinear_xcoord_r [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h : satisfiesLinear w (ecdsaLinearConstraints F z Q sig)) :
    w W_XCOORD_R = sig.r := by
  have h4 := h ⟨4, by unfold ecdsaLinearCount; omega⟩
  unfold satisfiesLinear ecdsaLinearConstraints ecdsaWitnessSize ecdsaLinearCount at h4
  simp only [Fin.sum_univ_eight, Fin.isValue] at h4
  simp only [W_XCOORD_R]; simp at h4; exact h4

-- ============================================================
-- Section 2: Quadratic constraint extraction lemmas
-- ============================================================

/-- Extract s * s_inv equation from quadratic constraint satisfaction. -/
theorem ecdsaQuad_s_sinv
    (w : Fin ecdsaWitnessSize → F)
    (h : ∀ i, satisfiesQuad w (ecdsaQuadConstraints i)) :
    w W_SIG_S * w W_SINV_L = w W_S_PRODUCT := by
  have := h ⟨0, by unfold ecdsaQuadCount; omega⟩
  simp only [ecdsaQuadConstraints, satisfiesQuad, W_SIG_S, W_SINV_L, W_S_PRODUCT] at this
  exact this

/-- Extract u1 = z * s_inv from quadratic constraint satisfaction. -/
theorem ecdsaQuad_u1
    (w : Fin ecdsaWitnessSize → F)
    (h : ∀ i, satisfiesQuad w (ecdsaQuadConstraints i)) :
    w W_MSG_Z * w W_SINV_L = w W_U1_VAL := by
  have := h ⟨1, by unfold ecdsaQuadCount; omega⟩
  simp only [ecdsaQuadConstraints, satisfiesQuad, W_MSG_Z, W_SINV_L, W_U1_VAL] at this
  exact this

/-- Extract u2 = r * s_inv from quadratic constraint satisfaction. -/
theorem ecdsaQuad_u2
    (w : Fin ecdsaWitnessSize → F)
    (h : ∀ i, satisfiesQuad w (ecdsaQuadConstraints i)) :
    w W_SIG_R * w W_SINV_L = w W_U2_VAL := by
  have := h ⟨2, by unfold ecdsaQuadCount; omega⟩
  simp only [ecdsaQuadConstraints, satisfiesQuad, W_SIG_R, W_SINV_L, W_U2_VAL] at this
  exact this

-- ============================================================
-- Section 3: Main bridge theorem
-- ============================================================

/-- **ECDSA constraint bridge**: if the witness satisfies all linear and
    quadratic ECDSA constraints, then `ecdsaVerify z Q sig` holds.

    The proof chains:
    1. Linear: w[SIG_S] = sig.s, w[S_PRODUCT] = 1
    2. Quadratic: w[SIG_S] * w[SINV] = w[S_PRODUCT]
    3. Combined: sig.s * w[SINV] = 1, hence sig.s ≠ 0
    4. Linear: w[XCOORD_R] = sig.r
    5. Since w[XCOORD_R] represents xCoord(R), we get xCoord(R) = sig.r
    6. sig.s ≠ 0 ∧ xCoord(R) = sig.r → ecdsaVerify -/
theorem ecdsaConstraints_imply_verify [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (h_lin : satisfiesLinear w (ecdsaLinearConstraints F z Q sig))
    (h_quad : ∀ i, satisfiesQuad w (ecdsaQuadConstraints i))
    (hxcoord : w W_XCOORD_R = ecdsaRecoveryXCoord z Q sig) :
    ecdsaVerify z Q sig := by
  have h_s := ecdsaLinear_sig_s z Q sig w h_lin
  have h_prod := ecdsaLinear_s_product z Q sig w h_lin
  have h_mul := ecdsaQuad_s_sinv w h_quad
  have h_one : sig.s * w W_SINV_L = 1 := by rw [← h_s, h_mul, h_prod]
  have hs_ne : sig.s ≠ 0 := left_ne_zero_of_mul_eq_one h_one
  have h_xc := ecdsaLinear_xcoord_r z Q sig w h_lin
  have hxeq : ecdsaRecoveryXCoord z Q sig = sig.r := by rw [← hxcoord, h_xc]
  rw [ecdsaVerify_iff]
  exact ⟨hs_ne, hxeq⟩

-- ============================================================
-- Section 4: Structural witness bridge (eliminates hxcoord)
-- ============================================================

/-- **Structural ECDSA bridge**: if `ECDSAWitnessValid` is satisfied,
    then `ecdsaVerify z Q sig` holds.

    This eliminates the `hxcoord` hypothesis by deriving the x-coordinate
    match from the structural EC computation encoded in the witness.
    The proof delegates to `ecdsaConstraint_implies_verify` from
    `Circuit.lean`, which already proves the full extraction. -/
theorem ecdsaWitnessValid_implies_verify [EllipticCurveGroup F] [Fintype F]
    [CurveInstantiation F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (n : ℕ) (hs_ne : sig.s ≠ 0) (wv : ECDSAWitnessValid F z Q sig n) :
    ecdsaVerify z Q sig := by
  have bridge := ecdsaScalarComputation_implies_bridge F z sig wv.scalar_comp wv.hs_nonzero
  exact ecdsaConstraintNoInv_implies_verify n z Q sig wv.wit wv.hn hs_ne
    (by rw [wv.u1_wire_eq, bridge.1]) (by rw [wv.u2_wire_eq, bridge.2]) wv.constraint_sat

-- ============================================================
-- Section 5: Completeness (honest witness satisfies constraints)
-- ============================================================

/-- Completeness: the honest witness satisfies all quadratic ECDSA constraints. -/
theorem ecdsaHonestWitness_quad [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (xR : F) :
    ∀ i, satisfiesQuad (ecdsaHonestWitness F z Q sig xR) (ecdsaQuadConstraints i) := by
  intro i; fin_cases i <;>
    simp [satisfiesQuad, ecdsaQuadConstraints, ecdsaHonestWitness,
      W_SIG_S, W_SINV_L, W_S_PRODUCT, W_MSG_Z, W_U1_VAL, W_SIG_R, W_U2_VAL]

/-- The honest witness correctly sets the xCoord wire. -/
theorem ecdsaHonestWitness_xcoord [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (xR : F) :
    ecdsaHonestWitness F z Q sig xR W_XCOORD_R = xR := by
  simp [ecdsaHonestWitness, W_XCOORD_R]

/-- Completeness: the honest witness satisfies all linear ECDSA constraints
    when ecdsaVerify holds. -/
theorem ecdsaHonestWitness_linear [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hv : ecdsaVerify z Q sig) :
    satisfiesLinear (ecdsaHonestWitness F z Q sig (ecdsaRecoveryXCoord z Q sig))
      (ecdsaLinearConstraints F z Q sig) := by
  have ⟨hs_ne, hxr⟩ := (ecdsaVerify_iff z Q sig).mp hv
  intro i
  unfold ecdsaLinearConstraints ecdsaHonestWitness ecdsaWitnessSize ecdsaLinearCount
  rw [Fin.sum_univ_eight]
  fin_cases i <;> simp [mul_inv_cancel₀ hs_ne, hxr]
