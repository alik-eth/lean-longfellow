import LeanLongfellow.Ligero.ECDSABridge
import LeanLongfellow.Ligero.ProbabilisticBinding

set_option autoImplicit false

/-! # ECDSA Probabilistic Soundness via Ligero

Composes the ECDSA constraint bridge with Ligero probabilistic binding
to get: if the Ligero verifier accepts with good challenges, and the
witness encodes the correct recovery point x-coordinate, then
`ecdsaVerify` holds. -/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Soundness via contrapositive
-- ============================================================

/-- **ECDSA Ligero soundness**: if `niLigeroVerify` accepts on the ECDSA
    constraint system and the challenges avoid the bad set, then
    `ecdsaVerify` holds (assuming the witness correctly encodes xCoord(R)).

    This provides an extraction path that does NOT use `ecdsaCoefficient`
    or any Lean-level `if`. The ECDSA parameters (sig.s, z, sig.r) are
    embedded as TARGET VALUES in the linear constraints, not as
    polynomial coefficients. -/
theorem ecdsa_ligero_soundness [EllipticCurveGroup F]
    {params : LigeroParams}
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (niProof : NILigeroProof F params ecdsaLinearCount ecdsaWitnessSize ecdsaQuadCount)
    (haccept : niLigeroVerify w (ecdsaLinearConstraints F z Q sig)
      ecdsaQuadConstraints niProof)
    (h_lin_good : ¬ satisfiesLinear w (ecdsaLinearConstraints F z Q sig) →
      ¬ linearTestSingleChallenge w (ecdsaLinearConstraints F z Q sig) niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (ecdsaQuadConstraints i)) →
      ¬ quadTestSingleChallenge w ecdsaQuadConstraints niProof.u)
    (hxcoord : w W_XCOORD_R = ecdsaRecoveryXCoord z Q sig) :
    ecdsaVerify z Q sig := by
  have h_sat := niLigero_contrapositive w
    (ecdsaLinearConstraints F z Q sig) ecdsaQuadConstraints
    niProof haccept h_lin_good h_quad_good
  exact ecdsaConstraints_imply_verify z Q sig w h_sat.1
    (fun i => h_sat.2 i) hxcoord

-- ============================================================
-- Section 2: Error bound
-- ============================================================

variable [DecidableEq F] [Fintype F]

open Classical in
/-- Error bound for the ECDSA Ligero test: if the witness does NOT
    satisfy all constraints, the bad challenge set is bounded. -/
theorem ecdsa_ligero_error_bound [EllipticCurveGroup F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (w : Fin ecdsaWitnessSize → F)
    (hviol : ¬ satisfiesAll w (ecdsaLinearConstraints F z Q sig) ecdsaQuadConstraints) :
    countSat (fun alpha =>
      linearTestSingleChallenge w (ecdsaLinearConstraints F z Q sig) alpha) ≤
        Fintype.card F ^ (ecdsaLinearCount - 1) ∨
    countSat (fun u =>
      quadTestSingleChallenge w ecdsaQuadConstraints u) ≤
        Fintype.card F ^ (ecdsaQuadCount - 1) :=
  niLigero_combined_error w (ecdsaLinearConstraints F z Q sig) ecdsaQuadConstraints hviol
