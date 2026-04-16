import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.ECDSAModular
import LeanLongfellow.Circuit.ECDSA.Spec
import LeanLongfellow.Circuit.ECDSA.Circuit

set_option autoImplicit false

open Finset

/-! # ECDSA Ligero Constraint System

Encodes ECDSA verification as linear + quadratic constraints over a
flat witness vector, suitable for verification via the Ligero IOP.

This provides an alternative extraction path that does NOT use the
`ecdsaCoefficient` lookup table. Instead, the ECDSA predicate is
decomposed into:
- **Quadratic constraints**: `s * s_inv`, `z * s_inv`, `r * s_inv`
- **Linear constraints**: input assignments (`w[s_idx] = sig.s`),
  product checks (`w[product_idx] = 1`), x-coordinate match
  (`w[xcoord_idx] = sig.r`)

Combined, satisfaction of all constraints implies `ecdsaVerify`. -/

variable (F : Type*) [Field F]

/-- Number of wire positions in the ECDSA Ligero witness.
    Layout:
    - 0: sig.s           (public input)
    - 1: sig.s⁻¹         (private witness)
    - 2: z               (public input: message hash)
    - 3: sig.r           (public input)
    - 4: s * s_inv       (intermediate: should be 1)
    - 5: u1 = z * s_inv  (intermediate)
    - 6: u2 = r * s_inv  (intermediate)
    - 7: xCoord(R)       (intermediate: recovery point x-coord) -/
def ecdsaWitnessSize : ℕ := 8

-- Wire position indices
def W_SIG_S : Fin ecdsaWitnessSize := ⟨0, by unfold ecdsaWitnessSize; omega⟩
def W_SINV_L : Fin ecdsaWitnessSize := ⟨1, by unfold ecdsaWitnessSize; omega⟩
def W_MSG_Z : Fin ecdsaWitnessSize := ⟨2, by unfold ecdsaWitnessSize; omega⟩
def W_SIG_R : Fin ecdsaWitnessSize := ⟨3, by unfold ecdsaWitnessSize; omega⟩
def W_S_PRODUCT : Fin ecdsaWitnessSize := ⟨4, by unfold ecdsaWitnessSize; omega⟩
def W_U1_VAL : Fin ecdsaWitnessSize := ⟨5, by unfold ecdsaWitnessSize; omega⟩
def W_U2_VAL : Fin ecdsaWitnessSize := ⟨6, by unfold ecdsaWitnessSize; omega⟩
def W_XCOORD_R : Fin ecdsaWitnessSize := ⟨7, by unfold ecdsaWitnessSize; omega⟩

/-- Quadratic constraints for ECDSA field operations.
    - QC 0: w[SIG_S] * w[SINV] = w[S_PRODUCT]   (s * s⁻¹)
    - QC 1: w[MSG_Z] * w[SINV] = w[U1_VAL]       (z * s⁻¹ = u1)
    - QC 2: w[SIG_R] * w[SINV] = w[U2_VAL]       (r * s⁻¹ = u2) -/
def ecdsaQuadCount : ℕ := 3

def ecdsaQuadConstraints : Fin ecdsaQuadCount → QuadConstraint ecdsaWitnessSize
  | ⟨0, _⟩ => ⟨W_SIG_S, W_SINV_L, W_S_PRODUCT⟩
  | ⟨1, _⟩ => ⟨W_MSG_Z, W_SINV_L, W_U1_VAL⟩
  | ⟨2, _⟩ => ⟨W_SIG_R, W_SINV_L, W_U2_VAL⟩

/-- Number of linear constraints for ECDSA.
    - LC 0: w[SIG_S] = sig.s         (input assignment)
    - LC 1: w[MSG_Z] = z             (input assignment)
    - LC 2: w[SIG_R] = sig.r         (input assignment)
    - LC 3: w[S_PRODUCT] = 1         (s * s_inv forced to 1)
    - LC 4: w[XCOORD_R] = sig.r      (x-coordinate match) -/
def ecdsaLinearCount : ℕ := 5

/-- The ECDSA linear constraint matrix and target vector.
    Each row has a single 1 in the relevant column, and the target
    is the expected value. This encodes input assignments and the
    x-coordinate check. -/
noncomputable def ecdsaLinearConstraints [EllipticCurveGroup F]
    (z : F) (_Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) :
    LinearConstraints F ecdsaLinearCount ecdsaWitnessSize where
  matrix := fun row col =>
    match row.val, col.val with
    | 0, 0 => 1  -- w[SIG_S]
    | 1, 2 => 1  -- w[MSG_Z]
    | 2, 3 => 1  -- w[SIG_R]
    | 3, 4 => 1  -- w[S_PRODUCT]
    | 4, 7 => 1  -- w[XCOORD_R]
    | _, _ => 0
  target := fun row =>
    match row.val with
    | 0 => sig.s
    | 1 => z
    | 2 => sig.r
    | 3 => 1
    | 4 => sig.r  -- xCoord(R) must equal sig.r
    | _ => 0      -- unreachable for Fin 5

/-- Construct the honest ECDSA witness from valid parameters.
    Used for completeness (honest prover can satisfy all constraints). -/
noncomputable def ecdsaHonestWitness [EllipticCurveGroup F]
    (z : F) (_Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (xcoord_R : F) : Fin ecdsaWitnessSize → F
  | ⟨0, _⟩ => sig.s
  | ⟨1, _⟩ => sig.s⁻¹
  | ⟨2, _⟩ => z
  | ⟨3, _⟩ => sig.r
  | ⟨4, _⟩ => sig.s * sig.s⁻¹
  | ⟨5, _⟩ => z * sig.s⁻¹
  | ⟨6, _⟩ => sig.r * sig.s⁻¹
  | ⟨7, _⟩ => xcoord_R

-- ============================================================
-- Section: Structural ECDSA Witness
-- ============================================================

/-- **Structural ECDSA witness validity.**

    Packages a circuit-level `ECDSAWitness` together with all correctness
    properties needed to derive `ecdsaVerify` without any external
    `hxcoord` hypothesis.  The key idea is that the EC computation
    (scalar multiplications + point addition) is encoded structurally
    via `ecdsaConstraint`, and the scalar-field bridges are derived
    from a transparent `ECDSAScalarComputation` that decomposes the
    modular arithmetic into verifiable sub-claims.

    From these fields, `ecdsaConstraint_implies_verify` directly yields
    `ecdsaVerify z Q sig`. -/
structure ECDSAWitnessValid (F : Type*) [Field F]
    [ec : EllipticCurveGroup F] [Fintype F] [CurveInstantiation F]
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (n : ℕ) where
  /-- The circuit-level witness with all intermediate EC values. -/
  wit : ECDSAWitness F n
  /-- Bit length is sufficient for the field. -/
  hn : 2 ^ n ≤ Fintype.card F
  /-- The circuit constraint system is satisfied. -/
  constraint_sat : ecdsaConstraint CurveInstantiation.params n z
    CurveInstantiation.generatorPoint (CurveInstantiation.toECPoint Q)
    sig.r sig.s wit
  /-- Decomposed scalar computation with explicit modular reductions. -/
  scalar_comp : ECDSAScalarComputation F z sig
  /-- `s` is nonzero in the scalar field (needed for inverse). -/
  hs_nonzero : (ec.fieldToNat sig.s : ZMod ec.groupOrder) ≠ 0
  /-- Circuit wire u1 agrees with the computed scalar. -/
  u1_wire_eq : ec.fieldToNat wit.u1 = scalar_comp.u1_product_red.rem
  /-- Circuit wire u2 agrees with the computed scalar. -/
  u2_wire_eq : ec.fieldToNat wit.u2 = scalar_comp.u2_product_red.rem
