import LeanLongfellow.Circuit.ECArith
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-! # Bridge: EC Gadgets ↔ Mathlib Weierstrass Curve Formulas

Connects `ECArith.lean`'s constraint-based EC operations to Mathlib's
`WeierstrassCurve.Affine` formulas (`slope`, `addX`, `addY`).

The key insight: our circuit constraints use *division-free* formulas
(e.g. `λ · (x₂ - x₁) = y₂ - y₁`) whereas Mathlib uses the rational form
(`(y₁ - y₂) / (x₁ - x₂)`).  We show these are equivalent when the
denominators are nonzero, and that the resulting x₃/y₃ coordinates agree.

All theorems work in the short Weierstrass specialisation
`a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b`.
-/

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

-- ============================================================
-- Section 1: Short Weierstrass as WeierstrassCurve
-- ============================================================

/-- Embed our short-Weierstrass `CurveParams` into Mathlib's general
    Weierstrass form.  Sets `a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b`. -/
def CurveParams.toWeierstrass (params : CurveParams F) : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := params.a
  a₆ := params.b

@[simp]
theorem CurveParams.toWeierstrass_a₁ (params : CurveParams F) :
    params.toWeierstrass.a₁ = 0 := rfl

@[simp]
theorem CurveParams.toWeierstrass_a₂ (params : CurveParams F) :
    params.toWeierstrass.a₂ = 0 := rfl

@[simp]
theorem CurveParams.toWeierstrass_a₃ (params : CurveParams F) :
    params.toWeierstrass.a₃ = 0 := rfl

@[simp]
theorem CurveParams.toWeierstrass_a₄ (params : CurveParams F) :
    params.toWeierstrass.a₄ = params.a := rfl

@[simp]
theorem CurveParams.toWeierstrass_a₆ (params : CurveParams F) :
    params.toWeierstrass.a₆ = params.b := rfl

-- ============================================================
-- Section 2: Short Weierstrass simplifications
-- ============================================================

/-- In short Weierstrass form, `negY x y = -y`. -/
theorem shortWeierstrass_negY (params : CurveParams F) (x y : F) :
    params.toWeierstrass.negY x y = -y := by
  simp [negY]

/-- In short Weierstrass form, `addX x₁ x₂ ℓ = ℓ² - x₁ - x₂`. -/
theorem shortWeierstrass_addX (params : CurveParams F) (x₁ x₂ ℓ : F) :
    params.toWeierstrass.addX x₁ x₂ ℓ = ℓ ^ 2 - x₁ - x₂ := by
  simp [addX]

/-- In short Weierstrass form, `addY x₁ x₂ y₁ ℓ = ℓ · (x₁ - addX) - y₁`. -/
theorem shortWeierstrass_addY (params : CurveParams F) (x₁ x₂ y₁ ℓ : F) :
    params.toWeierstrass.addY x₁ x₂ y₁ ℓ =
      ℓ * (x₁ - params.toWeierstrass.addX x₁ x₂ ℓ) - y₁ := by
  simp [addY, negAddY, negY]
  ring

-- ============================================================
-- Section 3: Slope agreement (addition, x₁ ≠ x₂)
-- ============================================================

/-- Our addition constraint's implicit slope agrees with Mathlib's
    explicit `slope` when `x₁ ≠ x₂`.

    Constraint: `λ · (x₂ - x₁) = y₂ - y₁`
    Mathlib:    `slope = (y₁ - y₂) / (x₁ - x₂)`

    These are equal because `(y₂-y₁)/(x₂-x₁) = (y₁-y₂)/(x₁-x₂)`. -/
theorem ecAdd_slope_eq_mathlibSlope (params : CurveParams F)
    (x₁ x₂ y₁ y₂ lambda : F) (hne : x₁ ≠ x₂)
    (hslope : lambda * (x₂ - x₁) = y₂ - y₁) :
    lambda = params.toWeierstrass.slope x₁ x₂ y₁ y₂ := by
  rw [slope_of_X_ne hne]
  have hne' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne
  rw [eq_div_iff hne']
  have hne'' : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have := mul_right_cancel₀ hne'' (by ring_nf; rw [hslope]; ring : lambda * (x₁ - x₂) * (x₂ - x₁) = (y₁ - y₂) * (x₂ - x₁))
  linarith

-- ============================================================
-- Section 4: x-coordinate agreement (addition)
-- ============================================================

/-- The x-coordinate from our addition constraint matches Mathlib's `addX`
    for short Weierstrass.

    Constraint: `x₃ = λ² - x₁ - x₂`
    Mathlib:    `addX x₁ x₂ ℓ = ℓ² - x₁ - x₂` (short Weierstrass) -/
theorem ecAdd_x_eq_mathlibAddX (params : CurveParams F)
    (x₁ x₂ x₃ lambda : F)
    (hx3 : x₃ = lambda * lambda - x₁ - x₂) :
    x₃ = params.toWeierstrass.addX x₁ x₂ lambda := by
  rw [shortWeierstrass_addX, hx3, sq]

-- ============================================================
-- Section 5: y-coordinate agreement (addition)
-- ============================================================

/-- The y-coordinate from our addition constraint matches Mathlib's `addY`
    for short Weierstrass.

    Constraint: `y₃ = λ · (x₁ - x₃) - y₁`
    Mathlib:    `addY x₁ x₂ y₁ ℓ = ℓ · (x₁ - addX) - y₁` (short Weierstrass) -/
theorem ecAdd_y_eq_mathlibAddY (params : CurveParams F)
    (x₁ x₂ x₃ y₁ y₃ lambda : F)
    (hx3 : x₃ = lambda * lambda - x₁ - x₂)
    (hy3 : y₃ = lambda * (x₁ - x₃) - y₁) :
    y₃ = params.toWeierstrass.addY x₁ x₂ y₁ lambda := by
  rw [shortWeierstrass_addY, hy3]
  congr 1
  congr 1
  congr 1
  rw [shortWeierstrass_addX, hx3, sq]

-- ============================================================
-- Section 6: Full addition bridge
-- ============================================================

/-- If `ecAddConstraint` holds with `x₁ ≠ x₂`, then the result's
    coordinates agree with Mathlib's addition formulas for
    short Weierstrass curves.

    This is the main bridge theorem for point addition: our
    division-free constraint system computes the same (x₃, y₃) as
    Mathlib's rational-form group law. -/
theorem ecAddConstraint_matches_mathlib (params : CurveParams F)
    (p1 p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (hne : p1.x ≠ p2.x) :
    lambda = params.toWeierstrass.slope p1.x p2.x p1.y p2.y ∧
    p3.x = params.toWeierstrass.addX p1.x p2.x lambda ∧
    p3.y = params.toWeierstrass.addY p1.x p2.x p1.y lambda := by
  obtain ⟨_, _, _, hslope, hx3, hy3⟩ := hadd
  exact ⟨ecAdd_slope_eq_mathlibSlope params _ _ _ _ _ hne hslope,
         ecAdd_x_eq_mathlibAddX params _ _ _ _ hx3,
         ecAdd_y_eq_mathlibAddY params _ _ _ _ _ _ hx3 hy3⟩

-- ============================================================
-- Section 7: Slope agreement (doubling)
-- ============================================================

/-- Our doubling constraint's implicit slope agrees with Mathlib's
    `slope` in the tangent case when `y₁ ≠ 0` (short Weierstrass).

    Constraint: `λ · (2 · y₁) = 3 · x₁² + a`
    Mathlib:    `slope x₁ x₁ y₁ y₂ = (3x₁² + a₄) / (2y₁)` (short Weierstrass, `y₁ ≠ -y₂`) -/
theorem ecDouble_slope_eq_mathlibSlope (params : CurveParams F)
    (x₁ y₁ y₂ lambda : F) (hny : y₁ ≠ 0)
    (hslope : lambda * (2 * y₁) = 3 * x₁ * x₁ + params.a) :
    lambda = params.toWeierstrass.slope x₁ x₁ y₁ y₂ := by
  have hny' : y₁ ≠ params.toWeierstrass.negY x₁ y₂ := by
    simp [shortWeierstrass_negY]
    intro heq
    apply hny
    linarith
  rw [slope_of_Y_ne rfl hny']
  simp [shortWeierstrass_negY, CurveParams.toWeierstrass]
  rw [eq_div_iff (by linarith [hny] : (2 : F) * y₁ ≠ 0)]
  linarith

-- ============================================================
-- Section 8: Full doubling bridge
-- ============================================================

/-- If `ecDoubleConstraint` holds with `y₁ ≠ 0`, then the result's
    coordinates agree with Mathlib's tangent-line formulas for
    short Weierstrass curves.

    This is the main bridge theorem for point doubling. -/
theorem ecDoubleConstraint_matches_mathlib (params : CurveParams F)
    (p1 p3 : ECPoint F) (lambda : F) (y₂ : F)
    (hdbl : ecDoubleConstraint params p1 p3 lambda)
    (hny : p1.y ≠ 0) :
    lambda = params.toWeierstrass.slope p1.x p1.x p1.y y₂ ∧
    p3.x = params.toWeierstrass.addX p1.x p1.x lambda ∧
    p3.y = params.toWeierstrass.addY p1.x p1.x p1.y lambda := by
  obtain ⟨_, _, hslope, hx3, hy3⟩ := hdbl
  refine ⟨ecDouble_slope_eq_mathlibSlope params _ _ y₂ _ hny hslope, ?_, ?_⟩
  · rw [shortWeierstrass_addX, hx3, sq]
    ring
  · rw [shortWeierstrass_addY, hy3]
    congr 1; congr 1; congr 1
    rw [shortWeierstrass_addX, hx3, sq]; ring

-- ============================================================
-- Section 9: Curve equation agreement
-- ============================================================

/-- Our `ecPointValid` curve equation matches Mathlib's `Equation`
    for short Weierstrass form.

    Ours:    `y² = x³ + a·x + b`
    Mathlib: `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
    With `a₁=a₂=a₃=0, a₄=a, a₆=b` these coincide. -/
theorem ecPointValid_iff_mathlibEquation (params : CurveParams F)
    (x y : F) :
    (y * y = x * x * x + params.a * x + params.b) ↔
    params.toWeierstrass.Affine.Equation x y := by
  rw [Affine.equation_iff']
  simp [CurveParams.toWeierstrass]
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]
