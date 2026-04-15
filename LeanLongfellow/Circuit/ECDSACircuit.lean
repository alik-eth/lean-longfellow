import LeanLongfellow.Circuit.ECDSA
import LeanLongfellow.Circuit.ECArith

/-! # Concrete ECDSA Verification Circuit

Wires the EC arithmetic gadgets (`CurveParams`, `ECPoint`, `ecScalarMulChain`,
`ecAddFull`) into a concrete ECDSA verification constraint system, then proves
the extraction theorem connecting it to the abstract `ecdsaVerify` predicate.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: ECDSA Verification Constraint
-- ============================================================

/-- Witness data for the ECDSA verification circuit.
    Contains all intermediate values the prover must supply. -/
structure ECDSAWitness (F : Type*) [Field F] (n : ℕ) where
  s_inv : F
  u1 : F
  u2 : F
  -- Scalar multiplication witnesses for u1 · G
  u1_bits : Fin n → F
  G_intermediates : Fin (n + 1) → ECPoint F
  G_doubled : Fin n → ECPoint F
  G_double_lambdas : Fin n → F
  G_add_lambdas : Fin n → F
  -- Scalar multiplication witnesses for u2 · Q
  u2_bits : Fin n → F
  Q_intermediates : Fin (n + 1) → ECPoint F
  Q_doubled : Fin n → ECPoint F
  Q_double_lambdas : Fin n → F
  Q_add_lambdas : Fin n → F
  -- Final addition witness
  P1 : ECPoint F  -- = u1 · G
  P2 : ECPoint F  -- = u2 · Q
  R : ECPoint F   -- = P1 + P2
  final_lambda : F

/-- ECDSA verification as a system of field constraints.
    Given: message hash `z`, public key `Q`, signature `(r, s)`, curve params.
    Witnesses: `s_inv`, `u1`, `u2`, `R`, plus all intermediate EC witnesses.

    Constraints:
    1. `s * s_inv = 1`           (s is invertible)
    2. `u1 = z * s_inv`          (first scalar)
    3. `u2 = r * s_inv`          (second scalar)
    4. `P1 = u1 · G`             (scalar mul with generator)
    5. `P2 = u2 · Q`             (scalar mul with public key)
    6. `R = P1 + P2`             (point addition)
    7. `R.is_inf = 0 ∧ R.x = r`  (x-coordinate check) -/
def ecdsaConstraint (params : CurveParams F) (n : ℕ)
    (z : F) (G Q_pub : ECPoint F) (r s : F)
    (wit : ECDSAWitness F n) : Prop :=
  -- 1. s is invertible
  isNonzero s wit.s_inv ∧
  -- 2-3. Compute u1, u2
  wit.u1 = z * wit.s_inv ∧
  wit.u2 = r * wit.s_inv ∧
  -- 4. P1 = u1 · G (scalar multiplication)
  isBitDecomp wit.u1_bits wit.u1 ∧
  ecScalarMulChain params n wit.u1_bits G
    wit.G_intermediates wit.G_doubled wit.G_double_lambdas wit.G_add_lambdas ∧
  wit.P1 = wit.G_intermediates ⟨n, by omega⟩ ∧
  -- 5. P2 = u2 · Q (scalar multiplication)
  isBitDecomp wit.u2_bits wit.u2 ∧
  ecScalarMulChain params n wit.u2_bits Q_pub
    wit.Q_intermediates wit.Q_doubled wit.Q_double_lambdas wit.Q_add_lambdas ∧
  wit.P2 = wit.Q_intermediates ⟨n, by omega⟩ ∧
  -- 6. R = P1 + P2
  ecAddFull params wit.P1 wit.P2 wit.R wit.final_lambda ∧
  -- 7. x-coordinate check
  wit.R.is_inf = 0 ∧
  wit.R.x = r

-- ============================================================
-- Section 2: Bridge between abstract and concrete curve
-- ============================================================

/-- Connects abstract `EllipticCurve` operations to concrete
    `CurveParams`/`ECPoint` gadgets. The `_agree` fields are axioms
    that would be proven when instantiating a specific curve. -/
class CurveInstantiation (F : Type*) [Field F] [EllipticCurve F] where
  /-- Underlying curve parameters. -/
  params : CurveParams F
  /-- The generator as an ECPoint. -/
  generatorPoint : ECPoint F
  /-- Generator lies on the curve. -/
  generatorValid : ecPointValid params generatorPoint
  /-- Convert abstract Point to ECPoint. -/
  toECPoint : EllipticCurve.Point (F := F) → ECPoint F
  /-- x-coordinate agreement. -/
  xCoord_agree : ∀ (p : EllipticCurve.Point (F := F)), EllipticCurve.xCoord p = (toECPoint p).x
  /-- Generator agreement. -/
  generator_agree : toECPoint EllipticCurve.generator = generatorPoint
  /-- Scalar multiplication agreement: if ecScalarMulChain computes a
      result from bits of scalar and P, then the result matches the
      abstract scalarMul. -/
  scalarMul_agree : ∀ (scalar : F) (P : EllipticCurve.Point (F := F)) (n : ℕ)
    (bits : Fin n → F) (ints : Fin (n + 1) → ECPoint F)
    (dbl : Fin n → ECPoint F) (dl al : Fin n → F),
    isBitDecomp bits scalar →
    ecScalarMulChain params n bits (toECPoint P) ints dbl dl al →
    ints ⟨n, by omega⟩ = toECPoint (EllipticCurve.scalarMul scalar P)
  /-- Point addition agreement. -/
  pointAdd_agree : ∀ (P Q : EllipticCurve.Point (F := F))
    (p3 : ECPoint F) (lam : F),
    ecAddFull params (toECPoint P) (toECPoint Q) p3 lam →
    p3 = toECPoint (EllipticCurve.pointAdd P Q)
  /-- The abstract identity maps to the ECPoint infinity. -/
  identity_agree : (toECPoint EllipticCurve.identity).is_inf = 1
  /-- The abstract identity maps to the canonical ECPoint at infinity. -/
  identity_toECPoint : toECPoint EllipticCurve.identity = ⟨0, 0, 1⟩
  /-- Non-identity points have is_inf = 0. -/
  nonIdentity_is_fin : ∀ (p : EllipticCurve.Point (F := F)),
    p ≠ EllipticCurve.identity → (toECPoint p).is_inf = 0
  /-- Doubling at the constraint level matches abstract point doubling.
      When a finite point (toECPoint P) satisfies ecDoubleConstraint,
      the result equals toECPoint (pointAdd P P). -/
  doublePoint_agree : ∀ (P : EllipticCurve.Point (F := F))
    (d : ECPoint F) (lam : F),
    (toECPoint P).is_inf = 0 →
    ecDoubleConstraint params (toECPoint P) d lam →
    d = toECPoint (EllipticCurve.pointAdd P P)

-- ============================================================
-- Section 3: Extraction Theorem
-- ============================================================

/-- If the ECDSA constraint system is satisfied, then the abstract
    `ecdsaVerify` predicate holds. This provides the soundness-relevant
    extraction direction for `ECDSACircuitSpec`. -/
theorem ecdsaConstraint_implies_verify [EllipticCurve F] [inst : CurveInstantiation F]
    (n : ℕ) (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (wit : ECDSAWitness F n)
    (hcon : ecdsaConstraint inst.params n z
      inst.generatorPoint (inst.toECPoint Q)
      sig.r sig.s wit) :
    ecdsaVerify z Q sig := by
  obtain ⟨h_inv, h_u1, h_u2, h_u1bits, h_smG, h_P1, h_u2bits, h_smQ, h_P2,
          h_add, h_notinf, h_xr⟩ := hcon
  -- s ≠ 0
  have hne : sig.s ≠ 0 := isNonzero_ne_zero sig.s wit.s_inv h_inv
  -- s_inv = s⁻¹
  have hs_inv : wit.s_inv = sig.s⁻¹ := by
    have hmul : sig.s * wit.s_inv = 1 := h_inv
    have := mul_left_cancel₀ hne (show sig.s * wit.s_inv = sig.s * sig.s⁻¹ by
      rw [hmul, mul_inv_cancel₀ hne])
    exact this
  -- P1 = scalarMul u1 G  (using generator_agree to bridge)
  have hsmG' : ecScalarMulChain inst.params n wit.u1_bits
      (inst.toECPoint EllipticCurve.generator) wit.G_intermediates
      wit.G_doubled wit.G_double_lambdas wit.G_add_lambdas := by
    rwa [inst.generator_agree]
  have hP1 : wit.P1 = inst.toECPoint
      (EllipticCurve.scalarMul wit.u1 EllipticCurve.generator) := by
    rw [h_P1]
    exact inst.scalarMul_agree wit.u1 EllipticCurve.generator n
      wit.u1_bits wit.G_intermediates wit.G_doubled
      wit.G_double_lambdas wit.G_add_lambdas h_u1bits hsmG'
  -- P2 = scalarMul u2 Q
  have hP2 : wit.P2 = inst.toECPoint
      (EllipticCurve.scalarMul wit.u2 Q) := by
    rw [h_P2]
    exact inst.scalarMul_agree wit.u2 Q n
      wit.u2_bits wit.Q_intermediates wit.Q_doubled
      wit.Q_double_lambdas wit.Q_add_lambdas h_u2bits h_smQ
  -- R = pointAdd P1 P2
  have hR : wit.R = inst.toECPoint
      (EllipticCurve.pointAdd
        (EllipticCurve.scalarMul wit.u1 EllipticCurve.generator)
        (EllipticCurve.scalarMul wit.u2 Q)) := by
    rw [hP1, hP2] at h_add
    exact inst.pointAdd_agree _ _ wit.R wit.final_lambda h_add
  -- Unfold ecdsaVerify and prove both conjuncts
  unfold ecdsaVerify
  refine ⟨hne, ?_⟩
  -- After unfolding, the goal has let-bindings reducing to xCoord(R) = r
  -- We rewrite u1, u2 in terms of s_inv then use xCoord_agree
  simp only
  rw [← hs_inv, ← h_u1, ← h_u2]
  rw [inst.xCoord_agree, ← hR, h_xr]
