import LeanLongfellow.Circuit.ECDSA.Spec
import LeanLongfellow.Circuit.EC.ScalarMul
import LeanLongfellow.Field.P256
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # Concrete P-256 EllipticCurve Instance

Provides an `EllipticCurve F_p256` instance by embedding the NIST P-256
curve parameters into Mathlib's `WeierstrassCurve` and using the proven
`AddCommGroup` structure on `WeierstrassCurve.Affine.Point`.

## Curve parameters (short Weierstrass: y² = x³ + ax + b)

- a = -3 (mod p)
- b = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
- Gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
- Gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
-/

open WeierstrassCurve Affine

-- ============================================================
-- Section 1: P-256 Weierstrass curve definition
-- ============================================================

/-- The P-256 `b` coefficient. -/
def p256_b : ℕ :=
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- The P-256 generator x-coordinate. -/
def p256_Gx : ℕ :=
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

/-- The P-256 generator y-coordinate. -/
def p256_Gy : ℕ :=
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- The NIST P-256 curve as a Weierstrass curve over `F_p256`.
    Short Weierstrass form: `y² = x³ - 3x + b`, encoded as
    `a₁ = a₂ = a₃ = 0`, `a₄ = -3`, `a₆ = b`. -/
def p256WCurve : WeierstrassCurve F_p256 where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := (-3 : F_p256)
  a₆ := (p256_b : F_p256)

-- ============================================================
-- Section 2: Generator point on the curve
-- ============================================================

/-- The generator point `(Gx, Gy)` lies on the P-256 curve and is nonsingular.

    Both the curve equation and the partial-derivative condition are decidable
    equalities in `ZMod p256Prime`, verified by `native_decide`. -/
theorem p256_generator_nonsingular :
    Nonsingular p256WCurve (↑p256_Gx : F_p256) (↑p256_Gy : F_p256) := by
  rw [nonsingular_iff']
  refine ⟨?_, Or.inr ?_⟩
  · rw [equation_iff']
    native_decide
  · native_decide

/-- The P-256 generator point as a `WeierstrassCurve.Affine.Point`. -/
def p256Generator : Point p256WCurve :=
  Point.some (↑p256_Gx : F_p256) (↑p256_Gy : F_p256) p256_generator_nonsingular

-- ============================================================
-- Section 3: Helper: extract x-coordinate from a Point
-- ============================================================

/-- Extract the x-coordinate from a Weierstrass curve point.
    Returns `0` for the point at infinity. -/
def weierstrassXCoord : Point p256WCurve → F_p256
  | Point.zero => 0
  | Point.some x _ _ => x

-- ============================================================
-- Section 4: EllipticCurve instance
-- ============================================================

/-- Concrete P-256 instance of the abstract `EllipticCurve` class.

    - **Point**: `WeierstrassCurve.Affine.Point` on `p256WCurve`, which carries
      Mathlib's proven `AddCommGroup` structure.
    - **pointAdd**: the group addition `(· + ·)` from `AddCommGroup`.
    - **identity**: the zero element `Point.zero` (point at infinity).
    - **scalarMul**: takes `ℕ` and uses `AddCommGroup` scalar multiplication `n • P`.
    - **groupOrder**: the P-256 group order (distinct from the base field order `p`).
    - **fieldToNat**: `ZMod.val` — the canonical `[0, p)` representative.
    - **xCoord**: pattern-matches on `Point.zero` / `Point.some`.

    Group-law proof fields are separated into opaque `theorem`s below to
    prevent Lean from eagerly unfolding `AddCommGroup` machinery on the
    256-bit Weierstrass curve during typeclass synthesis, which causes
    memory blowup. -/

-- Opaque proof terms — prevents Lean from reducing through
-- AddCommGroup on the 256-bit Weierstrass curve at synthesis time.
private theorem p256_pointAdd_identity_left :
    ∀ P : Point p256WCurve, (Point.zero : Point p256WCurve) + P = P := zero_add

private theorem p256_pointAdd_identity_right :
    ∀ P : Point p256WCurve, P + (Point.zero : Point p256WCurve) = P := add_zero

private theorem p256_scalarMul_zero :
    ∀ P : Point p256WCurve, (0 : ℕ) • P = (Point.zero : Point p256WCurve) :=
  fun _ => zero_nsmul _

private theorem p256_scalarMul_succ :
    ∀ (n : ℕ) (P : Point p256WCurve), (n + 1) • P = P + n • P :=
  fun n P => succ_nsmul' P n

private theorem p256_pointAdd_comm :
    ∀ P Q : Point p256WCurve, P + Q = Q + P := add_comm

private theorem p256_fieldToNat_injective :
    Function.Injective (ZMod.val : F_p256 → ℕ) := ZMod.val_injective p256Prime

private theorem p256_pointAdd_assoc :
    ∀ P Q R : Point p256WCurve, P + Q + R = P + (Q + R) :=
  fun P Q R => @add_assoc (Point p256WCurve) _ P Q R

instance : EllipticCurve F_p256 where
  Point := Point p256WCurve
  generator := p256Generator
  groupOrder := p256GroupOrder
  hGroupOrder := ⟨p256GroupOrder_prime⟩
  scalarMul n P := n • P
  pointAdd := (· + ·)
  xCoord := weierstrassXCoord
  identity := Point.zero
  fieldToNat := ZMod.val
  pointAdd_identity_left := p256_pointAdd_identity_left
  pointAdd_identity_right := p256_pointAdd_identity_right
  scalarMul_zero := p256_scalarMul_zero
  scalarMul_succ := p256_scalarMul_succ
  pointAdd_comm := p256_pointAdd_comm
  fieldToNat_injective := p256_fieldToNat_injective

-- ============================================================
-- Section 5: EllipticCurveGroup instance
-- ============================================================

instance : EllipticCurveGroup F_p256 where
  pointAdd_assoc := p256_pointAdd_assoc
