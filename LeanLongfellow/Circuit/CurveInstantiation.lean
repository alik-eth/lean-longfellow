import LeanLongfellow.Circuit.ECBridge
import LeanLongfellow.Field.P256Curve

/-! # P-256 Curve Instantiation: Circuit EC ops ↔ Concrete EllipticCurve

Bridges the circuit-level EC operations (`ecAddConstraint`, `ecDoubleConstraint`)
to the concrete P-256 `EllipticCurve F_p256` instance by specialising the abstract
bridge theorems in `ECBridge.lean` to the P-256 curve parameters.

## Strategy

1. Define `p256CurveParams : CurveParams F_p256` matching the P-256 constants.
2. Show `p256CurveParams.toWeierstrass = p256WCurve`.
3. Embed circuit `ECPoint`s into Mathlib `Point p256WCurve` via `ECPoint.toP256Point`.
4. Prove circuit addition/doubling agrees with Mathlib's point addition.

Most proofs are rewriting: the abstract bridge does the hard work, we just
specialise to P-256 parameters and rewrite via `p256_params_match`.
-/

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

-- ============================================================
-- Section 1: P-256 CurveParams
-- ============================================================

/-- P-256 curve parameters for the circuit constraint system.
    `a = -3`, `b = p256_b` (the NIST constant). -/
def p256CurveParams : CurveParams F_p256 where
  a := -3
  b := (p256_b : F_p256)

-- ============================================================
-- Section 2: Parameter matching
-- ============================================================

/-- The circuit's `CurveParams.toWeierstrass` agrees with the concrete
    `p256WCurve` definition from `P256Curve.lean`. -/
theorem p256_params_match : p256CurveParams.toWeierstrass = p256WCurve := by
  ext <;> rfl

-- ============================================================
-- Section 3: Discriminant nonzero (axiom)
-- ============================================================

/-- The discriminant of `p256WCurve` is nonzero.

    For short Weierstrass `y² = x³ + ax + b`, the discriminant is
    `-16(4a³ + 27b²)`.  For P-256 this is a specific 256-bit
    nonzero value, verified here by `native_decide` over `ZMod p256Prime`. -/
theorem p256_discriminant_ne_zero : p256WCurve.Δ ≠ 0 := by native_decide

-- ============================================================
-- Section 4: ecPointValid implies Nonsingular on P-256
-- ============================================================

/-- On P-256, a valid circuit point (on the curve) is also nonsingular
    in the Mathlib sense, because the discriminant is nonzero. -/
theorem p256_ecPointValid_to_nonsingular (x y : F_p256)
    (hoc : y * y = x * x * x + p256CurveParams.a * x + p256CurveParams.b) :
    Nonsingular p256WCurve x y := by
  rw [← p256_params_match]
  exact (equation_iff_nonsingular_of_Δ_ne_zero
    (p256_params_match ▸ p256_discriminant_ne_zero)).mp
    ((ecPointValid_iff_mathlibEquation p256CurveParams x y).mp hoc)

-- ============================================================
-- Section 5: ECPoint to Point p256WCurve embedding
-- ============================================================

/-- Helper: extract the `is_inf = 0` case from `isBool` when `is_inf != 1`. -/
private theorem isBool_ne_one_eq_zero {x : F_p256} (hb : isBool x) (h1 : x ≠ 1) :
    x = 0 := by
  rcases (isBool_iff x).mp hb with h | h
  · exact h
  · exact absurd h h1

/-- Embed a circuit `ECPoint` into a Mathlib `Point p256WCurve`.

    - If `is_inf = 1` (point at infinity), maps to `Point.zero`.
    - If `is_inf = 0` (affine point on the curve), maps to `Point.some x y _`.

    Requires the point to be valid (`ecPointValid p256CurveParams`), which
    ensures the point lies on the curve and `is_inf` is boolean. -/
noncomputable def ECPoint.toP256Point (p : ECPoint F_p256)
    (hv : ecPointValid p256CurveParams p) : Point p256WCurve :=
  if hinf : p.is_inf = 1 then
    Point.zero
  else
    have h0 : p.is_inf = 0 := isBool_ne_one_eq_zero hv.1 hinf
    Point.some p.x p.y (p256_ecPointValid_to_nonsingular p.x p.y (hv.2 h0))

/-- When `is_inf = 0`, the embedding produces `Point.some`. -/
theorem ECPoint.toP256Point_some (p : ECPoint F_p256)
    (hv : ecPointValid p256CurveParams p) (h0 : p.is_inf = 0) :
    p.toP256Point hv = Point.some p.x p.y
      (p256_ecPointValid_to_nonsingular p.x p.y (hv.2 h0)) := by
  unfold toP256Point
  have h1 : p.is_inf ≠ 1 := by rw [h0]; exact one_ne_zero.symm
  rw [dif_neg h1]

/-- When `is_inf = 1`, the embedding produces `Point.zero`. -/
theorem ECPoint.toP256Point_zero (p : ECPoint F_p256)
    (hv : ecPointValid p256CurveParams p) (h1 : p.is_inf = 1) :
    p.toP256Point hv = Point.zero := by
  unfold toP256Point
  rw [dif_pos h1]

-- ============================================================
-- Section 6: Point.some equality helper
-- ============================================================

/-- Two `Point.some` values with equal x and y coordinates are equal.
    This is just injectivity of the `some` constructor (the nonsingularity
    proof is proof-irrelevant since `Nonsingular` is a `Prop`). -/
theorem p256_point_some_eq {x₁ y₁ x₂ y₂ : F_p256}
    {h₁ : Nonsingular p256WCurve x₁ y₁}
    {h₂ : Nonsingular p256WCurve x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

-- ============================================================
-- Section 7: Circuit addition = Mathlib Point addition (x1 != x2)
-- ============================================================

/-- Circuit addition constraint on valid P-256 points agrees with
    Mathlib's `Point` addition when `x1 != x2`.

    Proof outline:
    1. `ecAddConstraint_matches_mathlib` gives coordinate equalities with
       Mathlib's `slope`/`addX`/`addY` for `p256CurveParams.toWeierstrass`.
    2. `p256_params_match` rewrites to `p256WCurve`.
    3. Mathlib's `add_of_X_ne` shows `Point.some + Point.some` produces
       `Point.some (addX ...) (addY ...)` when `x1 != x2`.
    4. Coordinate equality gives point equality. -/
theorem p256_ecAdd_correct (p1 p2 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hv2 : ecPointValid p256CurveParams p2)
    (hv3 : ecPointValid p256CurveParams p3)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (hne : p1.x ≠ p2.x) :
    (ECPoint.toP256Point p3 hv3 : Point p256WCurve) =
      (ECPoint.toP256Point p1 hv1 : Point p256WCurve) +
      (ECPoint.toP256Point p2 hv2 : Point p256WCurve) := by
  -- Extract finiteness from the constraint (keep hadd for the bridge)
  have hinf1 := hadd.1
  have hinf2 := hadd.2.1
  have hinf3 := hadd.2.2.1
  -- Get the bridge result: coordinates match Mathlib's formulas
  have hbridge := ecAddConstraint_matches_mathlib p256CurveParams p1 p2 p3 lambda hadd hne
  obtain ⟨hslope, hx3, hy3⟩ := hbridge
  -- Rewrite from p256CurveParams.toWeierstrass to p256WCurve
  rw [p256_params_match] at hslope hx3 hy3
  -- Unfold the embeddings (all three points are finite)
  rw [ECPoint.toP256Point_some p1 hv1 hinf1,
      ECPoint.toP256Point_some p2 hv2 hinf2,
      ECPoint.toP256Point_some p3 hv3 hinf3]
  -- Apply Mathlib's add_of_X_ne
  rw [add_of_X_ne hne]
  -- Now both sides are Point.some with (possibly different) nonsingularity proofs.
  -- The coordinates match by the bridge theorem.
  apply p256_point_some_eq
  · rw [hx3, hslope]
  · rw [hy3, hslope]

-- ============================================================
-- Section 8: Circuit doubling = Mathlib Point addition P + P (2y != 0)
-- ============================================================

/-- Circuit doubling constraint on a valid P-256 point agrees with
    Mathlib's `Point` addition `P + P` when `2y1 != 0`.

    The hypothesis `p1.y + p1.y != 0` (i.e. `2y1 != 0`) ensures the
    tangent slope exists.  In short Weierstrass form, `negY x y = -y`,
    so `y != negY x y` reduces to `y != -y`, i.e. `2y != 0`.

    Proof outline: same as addition, but using `ecDoubleConstraint_matches_mathlib`
    and `add_self_of_Y_ne`. -/
theorem p256_ecDouble_correct (p1 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hv3 : ecPointValid p256CurveParams p3)
    (hdbl : ecDoubleConstraint p256CurveParams p1 p3 lambda)
    (hny : p1.y + p1.y ≠ 0) :
    (ECPoint.toP256Point p3 hv3 : Point p256WCurve) =
      (ECPoint.toP256Point p1 hv1 : Point p256WCurve) +
      (ECPoint.toP256Point p1 hv1 : Point p256WCurve) := by
  -- Extract finiteness
  have hinf1 := hdbl.1
  have hinf3 := hdbl.2.1
  -- Get the bridge result
  have hbridge := ecDoubleConstraint_matches_mathlib p256CurveParams p1 p3 lambda hdbl hny
  obtain ⟨hslope, hx3, hy3⟩ := hbridge
  -- Rewrite to p256WCurve
  rw [p256_params_match] at hslope hx3 hy3
  -- Unfold embeddings
  rw [ECPoint.toP256Point_some p1 hv1 hinf1,
      ECPoint.toP256Point_some p3 hv3 hinf3]
  -- In short Weierstrass, negY x y = -y, so y != negY x y iff y + y != 0
  have hyneg : p1.y ≠ negY p256WCurve p1.x p1.y := by
    rw [← p256_params_match, shortWeierstrass_negY]
    intro heq
    exact hny (by linear_combination heq)
  -- Apply Mathlib's add_self_of_Y_ne
  rw [add_self_of_Y_ne hyneg]
  apply p256_point_some_eq
  · rw [hx3, hslope]
  · rw [hy3, hslope]

-- ============================================================
-- Section 9: Correctness in terms of EllipticCurve.pointAdd
-- ============================================================

/-- Circuit addition matches `EllipticCurve.pointAdd` (the abstract interface).
    Since the `EllipticCurve F_p256` instance defines `pointAdd := (. + .)` and
    `Point := Point p256WCurve`, this follows from `p256_ecAdd_correct`. -/
theorem p256_ecAdd_matches_pointAdd (p1 p2 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hv2 : ecPointValid p256CurveParams p2)
    (hv3 : ecPointValid p256CurveParams p3)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (hne : p1.x ≠ p2.x) :
    ECPoint.toP256Point p3 hv3 =
      @EllipticCurve.pointAdd F_p256 _ _ (ECPoint.toP256Point p1 hv1) (ECPoint.toP256Point p2 hv2) :=
  p256_ecAdd_correct p1 p2 p3 lambda hv1 hv2 hv3 hadd hne

/-- Circuit doubling matches `EllipticCurve.pointAdd P P` (the abstract interface). -/
theorem p256_ecDouble_matches_pointAdd (p1 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hv3 : ecPointValid p256CurveParams p3)
    (hdbl : ecDoubleConstraint p256CurveParams p1 p3 lambda)
    (hny : p1.y + p1.y ≠ 0) :
    ECPoint.toP256Point p3 hv3 =
      @EllipticCurve.pointAdd F_p256 _ _ (ECPoint.toP256Point p1 hv1) (ECPoint.toP256Point p1 hv1) :=
  p256_ecDouble_correct p1 p3 lambda hv1 hv3 hdbl hny

-- ============================================================
-- Section 10: Validity preservation on P-256
-- ============================================================

/-- Circuit addition preserves validity on P-256 (specialisation of the
    generic `ecAddConstraint_valid`). -/
theorem p256_ecAdd_preserves_valid (p1 p2 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hv2 : ecPointValid p256CurveParams p2)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (hne : p1.x ≠ p2.x) :
    ecPointValid p256CurveParams p3 :=
  ecAddConstraint_valid p256CurveParams p1 p2 p3 lambda hv1 hv2 hadd hne

/-- Circuit doubling preserves validity on P-256 (specialisation of the
    generic `ecDoubleConstraint_valid`). -/
theorem p256_ecDouble_preserves_valid (p1 p3 : ECPoint F_p256) (lambda : F_p256)
    (hv1 : ecPointValid p256CurveParams p1)
    (hdbl : ecDoubleConstraint p256CurveParams p1 p3 lambda) :
    ecPointValid p256CurveParams p3 :=
  ecDoubleConstraint_valid p256CurveParams p1 p3 lambda hv1 hdbl
