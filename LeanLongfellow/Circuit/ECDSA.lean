import LeanLongfellow.Circuit.Composition

open Finset Polynomial MultilinearPoly

/-! # Abstract ECDSA Specification

Defines ECDSA verification abstractly over an elliptic curve and states:
if a correct circuit exists, Longfellow (GKR + sumcheck) soundness
guarantees the signature is valid — or a sumcheck challenge hit a root.

This is a **pure specification** — no concrete curve arithmetic, no
circuit construction. The `ECDSACircuitSpec` structure axiomatizes
the extraction property of a correct ECDSA circuit; building a
concrete instance is future work.
-/

-- ============================================================
-- Section 1: Abstract elliptic curve
-- ============================================================

/-- Abstract elliptic curve with the operations needed for ECDSA.
    Parameterized by the scalar field `F`. -/
class EllipticCurve (F : Type*) [Field F] where
  /-- Points on the curve (including the point at infinity). -/
  Point : Type
  /-- The generator point. -/
  generator : Point
  /-- Scalar multiplication: `n · P`. -/
  scalarMul : F → Point → Point
  /-- Point addition. -/
  pointAdd : Point → Point → Point
  /-- Extract the x-coordinate as a field element. -/
  xCoord : Point → F
  /-- The identity point (point at infinity). -/
  identity : Point

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
    `u₁ = z·s⁻¹` and `u₂ = r·s⁻¹`. -/
def ecdsaVerify [EllipticCurve F] (z : F) (Q : EllipticCurve.Point (F := F))
    (sig : ECDSASignature F) : Prop :=
  sig.s ≠ 0 ∧
  let s_inv := sig.s⁻¹
  let u₁ := z * s_inv
  let u₂ := sig.r * s_inv
  let R := EllipticCurve.pointAdd
    (EllipticCurve.scalarMul u₁ EllipticCurve.generator)
    (EllipticCurve.scalarMul u₂ Q)
  EllipticCurve.xCoord R = sig.r

-- ============================================================
-- Section 3: Circuit correctness specification
-- ============================================================

/-- Specification of a circuit that correctly implements ECDSA verification.

    The **extraction** property says: if all layers are consistent and the
    output gate evaluates to `1`, then the ECDSA signature is valid. This
    is the soundness-relevant direction.

    Constructing a concrete instance requires building the actual ECDSA
    arithmetic circuit, which is future work. -/
structure ECDSACircuitSpec (F : Type*) [Field F] [EllipticCurve F]
    (s NL : ℕ) where
  /-- The circuit layers. -/
  layers : Fin NL → CircuitLayer F s
  /-- Extraction: if the circuit is layer-consistent and the output
      gate evaluates to `1` at some target, then ECDSA verifies. -/
  extraction : ∀ (z : F) (Q : EllipticCurve.Point (F := F))
    (sig : ECDSASignature F)
    (values : Fin (NL + 1) → LayerValues F s)
    (target : Fin s → F),
    (∀ k : Fin NL, ∀ g : Fin s → Bool,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g) →
    (values ⟨0, by omega⟩).eval target = 1 →
    ecdsaVerify z Q sig

-- ============================================================
-- Section 4: End-to-end theorems
-- ============================================================

variable [DecidableEq F] [EllipticCurve F]

omit [DecidableEq F] in
/-- **ECDSA circuit extraction:** if a correct ECDSA circuit has all
    layers consistent and the output evaluates to `1`, the signature
    is valid. Direct from the spec. -/
theorem ecdsa_circuit_extraction {s NL : ℕ}
    (spec : ECDSACircuitSpec F s NL)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (values : Fin (NL + 1) → LayerValues F s)
    (target : Fin s → F)
    (hcons : ∀ k : Fin NL, ∀ g : Fin s → Bool,
      layerConsistent (spec.layers k) (values k.castSucc) (values k.succ) g)
    (hout : (values ⟨0, by omega⟩).eval target = 1) :
    ecdsaVerify z Q sig :=
  spec.extraction z Q sig values target hcons hout

/-- **ECDSA–Longfellow soundness:** if a correct ECDSA circuit exists
    and the GKR verifier accepts a claim that "the output is `1`"
    (signature valid) but ECDSA does *not* actually verify, then some
    sumcheck challenge hit a root of a nonzero degree-≤-2 polynomial.

    Proof strategy:
    1. `spec.extraction` + `hfalse` → the claimed output `1` does not
       match the actual circuit output → `hclaim_wrong`.
    2. `gkr_composition` → root hit. -/
theorem ecdsa_longfellow_soundness {s NL : ℕ}
    (spec : ECDSACircuitSpec F s NL)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
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
    exact hfalse (spec.extraction z Q sig values (targets ⟨0, hNL⟩) hcons heq.symm)
  exact gkr_composition spec.layers values targets claimed_vals reductions
    hs hNL hcons haccept hdeg hclaim_wrong
