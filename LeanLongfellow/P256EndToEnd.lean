import LeanLongfellow.EndToEnd
import LeanLongfellow.Field.P256Curve

/-! # P-256-Specific End-to-End Soundness

Thin specializations of the abstract zk-eIDAS soundness theorems
(`zkEidasFull_soundness_or_collision`, `zkEidasFull_soundness`) at the
concrete NIST P-256 curve.

The `EllipticCurve F_p256` and `EllipticCurveGroup F_p256` instances
(from `LeanLongfellow.Field.P256Curve`) are resolved automatically,
so the theorem types mention `F_p256` explicitly — proving the
framework works for a real, standards-grade elliptic curve with
Mathlib-verified group laws.
-/

-- ============================================================
-- Section 1: Collision-extracting soundness for P-256
-- ============================================================

open Classical in
/-- **P-256-specific zk-eIDAS soundness (collision-extracting).**

    Eliminates the abstract `[EllipticCurve F]` parameter — this theorem
    speaks directly about NIST P-256 with Mathlib-proven group laws.

    Either all five security properties hold (ECDSA validity, predicate
    binding, escrow integrity, nullifier binding, holder binding), or a
    concrete hash collision can be extracted. -/
theorem zkEidas_p256_soundness_or_collision
    [PoseidonHash F_p256 3] [PoseidonHash F_p256 1]
    [LinearOrder F_p256] [CRHash (EscrowFields F_p256) F_p256]
    {s NL : ℕ}
    (proof : ZkEidasFullProof F_p256 s NL)
    (hs : 0 < 2 * s)
    (hverify : zkEidasFullVerify proof hs) :
    (ecdsaVerify proof.z proof.Q proof.sig ∧
     predicateHolds proof.predSpec proof.cv' ∧
     proof.escrowOriginal = proof.escrowDecrypted ∧
     (proof.cred₁ = proof.cred₂ ∧ proof.contract₁ = proof.contract₂ ∧
       proof.salt₁ = proof.salt₂) ∧
     proof.attr₁ = proof.attr₂) ∨
    PoseidonCollision F_p256 3 ∨ PoseidonCollision F_p256 1 ∨
    CRHashCollision (EscrowFields F_p256) F_p256 :=
  zkEidasFull_soundness_or_collision proof hs hverify

-- ============================================================
-- Section 2: Soundness with hash injectivity for P-256
-- ============================================================

/-- **P-256-specific zk-eIDAS soundness (with hash injectivity).**

    The same five-property composition as the collision-extracting variant,
    but assuming hash collision resistance (injectivity) as explicit
    hypotheses.  All five security properties are then unconditional. -/
theorem zkEidas_p256_soundness
    [PoseidonHash F_p256 3] [PoseidonHash F_p256 1]
    [LinearOrder F_p256] [CRHash (EscrowFields F_p256) F_p256]
    {s NL : ℕ}
    (proof : ZkEidasFullProof F_p256 s NL)
    (hs : 0 < 2 * s)
    (hverify : zkEidasFullVerify proof hs)
    (hcr3 : Function.Injective (PoseidonHash.hash (F := F_p256) (n := 3)))
    (hcr1 : Function.Injective (PoseidonHash.hash (F := F_p256) (n := 1)))
    (hcr_escrow : Function.Injective (CRHash.hash (α := EscrowFields F_p256) (β := F_p256))) :
    ecdsaVerify proof.z proof.Q proof.sig ∧
    predicateHolds proof.predSpec proof.cv' ∧
    proof.escrowOriginal = proof.escrowDecrypted ∧
    (proof.cred₁ = proof.cred₂ ∧ proof.contract₁ = proof.contract₂ ∧
      proof.salt₁ = proof.salt₂) ∧
    proof.attr₁ = proof.attr₂ :=
  zkEidasFull_soundness proof hs hverify hcr3 hcr1 hcr_escrow
