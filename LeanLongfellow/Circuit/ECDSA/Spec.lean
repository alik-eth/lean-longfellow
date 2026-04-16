import LeanLongfellow.Circuit.Core.Composition
import Mathlib.Data.ZMod.Basic

open Finset Polynomial MultilinearPoly

/-! # Abstract ECDSA Specification

Defines ECDSA verification abstractly over an elliptic curve and states:
if a correct circuit exists, Longfellow (GKR + sumcheck) soundness
guarantees the signature is valid — or a sumcheck challenge hit a root.

This is a **pure specification** — no concrete curve arithmetic, no
circuit construction. The `ECDSACircuitSpec` structure axiomatizes
the extraction property of a correct ECDSA circuit.  Concrete instances
with proven extraction are provided in `Composition.lean` (s=1, NL=1)
and `GateComposition.lean` (s=5, NL=14n+7).
-/

-- ============================================================
-- Section 1: Abstract elliptic curve
-- ============================================================

/-- Abstract elliptic curve with the operations needed for ECDSA.
    Parameterized by the base field `F`. Scalar multiplication takes
    a natural number (not a field element) so that ECDSA scalars can
    be computed in `ZMod groupOrder` and then projected to `ℕ` via
    `ZMod.val`. -/
class EllipticCurve (F : Type*) [Field F] where
  /-- Points on the curve (including the point at infinity). -/
  Point : Type
  /-- The generator point. -/
  generator : Point
  /-- The group order (number of points on the curve). -/
  groupOrder : ℕ
  /-- The group order is prime. -/
  hGroupOrder : Fact (Nat.Prime groupOrder)
  /-- Scalar multiplication: `n • P`. Takes ℕ, not a field element,
      because ECDSA scalars live in `ZMod groupOrder`, not the base field. -/
  scalarMul : ℕ → Point → Point
  /-- Point addition. -/
  pointAdd : Point → Point → Point
  /-- Extract the x-coordinate as a field element. -/
  xCoord : Point → F
  /-- The identity point (point at infinity). -/
  identity : Point
  /-- Map a base-field element to its canonical natural-number representative.
      For `ZMod p` this is `ZMod.val`. Used to coerce base-field values into
      the scalar field `ZMod groupOrder` for ECDSA arithmetic. -/
  fieldToNat : F → ℕ
  /-- Point addition with identity (left). -/
  pointAdd_identity_left : ∀ P : Point, pointAdd identity P = P
  /-- Point addition with identity (right). -/
  pointAdd_identity_right : ∀ P : Point, pointAdd P identity = P
  /-- Scalar multiplication base case. -/
  scalarMul_zero : ∀ P : Point, scalarMul 0 P = identity
  /-- Scalar multiplication inductive step. -/
  scalarMul_succ : ∀ (n : ℕ) (P : Point), scalarMul (n + 1) P = pointAdd P (scalarMul n P)
  /-- Point addition is commutative. -/
  pointAdd_comm : ∀ P Q : Point, pointAdd P Q = pointAdd Q P
  /-- fieldToNat is injective (faithful representation). -/
  fieldToNat_injective : Function.Injective fieldToNat

/-- The `EllipticCurve` class extended with associativity, needed for
    the scalar multiplication proof.  The other group-law axioms
    (identity, commutativity) now live in `EllipticCurve` itself.
    Associativity is the remaining axiom satisfied by any `AddCommGroup`
    — in particular, by Mathlib's `WeierstrassCurve.Affine.Point`. -/
class EllipticCurveGroup (F : Type*) [Field F] extends EllipticCurve F where
  /-- Point addition is associative. -/
  pointAdd_assoc : ∀ (P Q R : Point), pointAdd (pointAdd P Q) R = pointAdd P (pointAdd Q R)

-- ============================================================
-- Section 2: ECDSA verification predicate
-- ============================================================

/-- An ECDSA signature: `(r, s)` pair. -/
structure ECDSASignature (F : Type*) where
  r : F
  s : F

variable {F : Type*} [Field F]

/-- ECDSA verification: given message hash `z`, public key `Q`, and
    signature `(r, s)`, check that `r = x(u₁·G + u₂·Q)` where
    `u₁ = z·s⁻¹ mod n` and `u₂ = r·s⁻¹ mod n`.

    The scalars `u₁`, `u₂` are computed in `ZMod groupOrder` (the
    curve's group order), NOT in the base field `F`. For P-256,
    `p ≠ n`, so computing inverses in `F` would be incorrect. -/
def ecdsaVerify [ec : EllipticCurveGroup F] (z : F) (Q : EllipticCurve.Point (F := F))
    (sig : ECDSASignature F) : Prop :=
  sig.s ≠ 0 ∧
  let n := ec.groupOrder
  have : Fact (Nat.Prime n) := ec.hGroupOrder
  let z_n : ZMod n := (ec.fieldToNat z : ZMod n)
  let r_n : ZMod n := (ec.fieldToNat sig.r : ZMod n)
  let s_n : ZMod n := (ec.fieldToNat sig.s : ZMod n)
  let s_inv := s_n⁻¹
  let u₁ := z_n * s_inv
  let u₂ := r_n * s_inv
  let R := EllipticCurve.pointAdd
    (EllipticCurve.scalarMul (ZMod.val u₁) EllipticCurve.generator)
    (EllipticCurve.scalarMul (ZMod.val u₂) Q)
  EllipticCurve.xCoord R = sig.r

-- ============================================================
-- Section 3: Circuit correctness specification
-- ============================================================

/-- Specification of a circuit that correctly implements ECDSA verification
    for a specific message hash `z`, public key `Q`, and signature `sig`.

    The **extraction** property says: if all layers are consistent and the
    output gate evaluates to `1`, then the ECDSA signature is valid. This
    is the soundness-relevant direction.

    The circuit is parameterized by `(z, Q, sig)` because a real verification
    circuit encodes the specific values being checked. This allows non-vacuous
    extraction: for a valid signature, the circuit CAN output `1`. -/
structure ECDSACircuitSpec (F : Type*) [Field F] [EllipticCurveGroup F]
    (s NL : ℕ) (z : F) (Q : EllipticCurve.Point (F := F))
    (sig : ECDSASignature F) where
  /-- The circuit layers. -/
  layers : Fin NL → CircuitLayer F s
  /-- Extraction: if the circuit is layer-consistent and the output
      gate evaluates to `1` at some target, then ECDSA verifies. -/
  extraction :
    ∀ (values : Fin (NL + 1) → LayerValues F s)
    (target : Fin s → F),
    (∀ k : Fin NL, ∀ g : Fin s → Bool,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g) →
    (values ⟨0, by omega⟩).eval target = 1 →
    ecdsaVerify z Q sig

-- ============================================================
-- Section 4: End-to-end theorems
-- ============================================================

variable [DecidableEq F] [EllipticCurveGroup F]

omit [DecidableEq F] in
/-- **ECDSA circuit extraction:** if a correct ECDSA circuit has all
    layers consistent and the output evaluates to `1`, the signature
    is valid. Direct from the spec. -/
theorem ecdsa_circuit_extraction {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (spec : ECDSACircuitSpec F s NL z Q sig)
    (values : Fin (NL + 1) → LayerValues F s)
    (target : Fin s → F)
    (hcons : ∀ k : Fin NL, ∀ g : Fin s → Bool,
      layerConsistent (spec.layers k) (values k.castSucc) (values k.succ) g)
    (hout : (values ⟨0, by omega⟩).eval target = 1) :
    ecdsaVerify z Q sig :=
  spec.extraction values target hcons hout

/-- **ECDSA–Longfellow soundness:** if a correct ECDSA circuit exists
    and the GKR verifier accepts a claim that "the output is `1`"
    (signature valid) but ECDSA does *not* actually verify, then some
    sumcheck challenge hit a root of a nonzero degree-≤-2 polynomial.

    Proof strategy:
    1. `spec.extraction` + `hfalse` → the claimed output `1` does not
       match the actual circuit output → `hclaim_wrong`.
    2. `gkr_composition` → root hit. -/
theorem ecdsa_longfellow_soundness {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (spec : ECDSACircuitSpec F s NL z Q sig)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → F))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s) (hNL : 0 < NL)
    -- All layers consistent
    (hcons : ∀ k : Fin NL, ∀ g : Fin s → Bool,
      layerConsistent (spec.layers k) (values k.castSucc) (values k.succ) g)
    -- All reductions accept
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (spec.layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    -- Degree bounds
    (hdeg : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    -- Output claim is 1 (signature allegedly valid)
    (hclaim : claimed_vals ⟨0, hNL⟩ = 1)
    -- But ECDSA doesn't actually verify
    (hfalse : ¬ ecdsaVerify z Q sig) :
    -- Then a sumcheck challenge hit a root
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((reductions k).rounds i).challenge = 0 := by
  -- The claimed output doesn't match the actual output
  have hclaim_wrong : claimed_vals ⟨0, hNL⟩ ≠
      (values ⟨0, by omega⟩).eval (targets ⟨0, hNL⟩) := by
    intro heq
    rw [hclaim] at heq
    exact hfalse (spec.extraction values (targets ⟨0, hNL⟩) hcons heq.symm)
  exact gkr_composition spec.layers values targets claimed_vals reductions
    hs hNL hcons haccept hdeg hclaim_wrong
