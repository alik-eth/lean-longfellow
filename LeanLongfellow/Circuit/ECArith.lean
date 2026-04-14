import LeanLongfellow.Circuit.Gadgets
import Mathlib.Tactic.LinearCombination

/-! # Elliptic Curve Arithmetic Gadgets for ECDSA Circuit Verification

Short Weierstrass curve operations expressed as constraint relations (Props)
over field elements. Each EC operation is a predicate on field elements with
a witness (the slope λ), following the same pattern as `word32Add` in Word32.lean.

Curve equation: `y² = x³ + a·x + b` over a field `F`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Curve Parameters
-- ============================================================

/-- Short Weierstrass curve parameters: `y² = x³ + a·x + b`. -/
structure CurveParams (F : Type*) [Field F] where
  a : F
  b : F

-- ============================================================
-- Section 2: Point Representation
-- ============================================================

/-- An affine point as field elements, with an "is_infinity" flag.
    `is_inf = 1` means point at infinity, `is_inf = 0` means affine `(x, y)`. -/
structure ECPoint (F : Type*) [Field F] where
  x : F
  y : F
  is_inf : F
  deriving DecidableEq

/-- An `ECPoint` is well-formed: `is_inf` is boolean, and if not infinity,
    the point lies on the curve. -/
def ecPointValid (params : CurveParams F) (p : ECPoint F) : Prop :=
  isBool p.is_inf ∧
  (p.is_inf = 0 → p.y * p.y = p.x * p.x * p.x + params.a * p.x + params.b)

-- ============================================================
-- Section 3: Point Addition Constraint
-- ============================================================

/-- Point addition constraint (general case: `P₁ ≠ P₂`, neither at infinity).
    The slope `λ` is a witness provided by the prover.

    Standard formulas (division-free):
    - `λ · (x₂ - x₁) = y₂ - y₁`
    - `x₃ = λ² - x₁ - x₂`
    - `y₃ = λ · (x₁ - x₃) - y₁` -/
def ecAddConstraint (p1 p2 p3 : ECPoint F) (lambda : F) : Prop :=
  -- Neither point is at infinity
  p1.is_inf = 0 ∧ p2.is_inf = 0 ∧ p3.is_inf = 0 ∧
  -- Slope: λ · (x₂ - x₁) = y₂ - y₁ (avoids division)
  lambda * (p2.x - p1.x) = p2.y - p1.y ∧
  -- x₃ = λ² - x₁ - x₂
  p3.x = lambda * lambda - p1.x - p2.x ∧
  -- y₃ = λ · (x₁ - x₃) - y₁
  p3.y = lambda * (p1.x - p3.x) - p1.y

-- ============================================================
-- Section 4: Point Doubling Constraint
-- ============================================================

/-- Point doubling constraint: `P₃ = 2 · P₁`.
    The slope `λ` is a witness.

    Standard formula (division-free):
    - `λ · (2 · y₁) = 3 · x₁² + a`
    - `x₃ = λ² - 2 · x₁`
    - `y₃ = λ · (x₁ - x₃) - y₁` -/
def ecDoubleConstraint (params : CurveParams F) (p1 p3 : ECPoint F) (lambda : F) : Prop :=
  p1.is_inf = 0 ∧ p3.is_inf = 0 ∧
  -- Slope: λ · (2 · y₁) = 3 · x₁² + a
  lambda * (2 * p1.y) = 3 * p1.x * p1.x + params.a ∧
  -- x₃ = λ² - 2 · x₁
  p3.x = lambda * lambda - 2 * p1.x ∧
  -- y₃ = λ · (x₁ - x₃) - y₁
  p3.y = lambda * (p1.x - p3.x) - p1.y

-- ============================================================
-- Section 5: Full Point Addition (handling infinity)
-- ============================================================

/-- Complete point addition handling all cases:
    - `P₁ = O` → result = `P₂`
    - `P₂ = O` → result = `P₁`
    - both finite, `x₁ = x₂`, `y₁ = -y₂` → result = `O`
    - both finite, `x₁ = x₂`, `y₁ = y₂` → doubling
    - both finite, `x₁ ≠ x₂` → general addition -/
def ecAddFull (params : CurveParams F) (p1 p2 p3 : ECPoint F) (lambda : F) : Prop :=
  -- Case: P1 is infinity
  (p1.is_inf = 1 → p3 = p2) ∧
  -- Case: P2 is infinity
  (p2.is_inf = 1 → p3 = p1) ∧
  -- Case: both finite, x₁ = x₂, y₁ = -y₂ → result is infinity
  (p1.is_inf = 0 → p2.is_inf = 0 → p1.x = p2.x → p1.y + p2.y = 0 →
    p3.is_inf = 1) ∧
  -- Case: both finite, x₁ = x₂, y₁ = y₂ → doubling
  (p1.is_inf = 0 → p2.is_inf = 0 → p1.x = p2.x → p1.y = p2.y →
    ecDoubleConstraint params p1 p3 lambda) ∧
  -- Case: both finite, x₁ ≠ x₂ → general addition
  (p1.is_inf = 0 → p2.is_inf = 0 → p1.x ≠ p2.x →
    ecAddConstraint p1 p2 p3 lambda)

-- ============================================================
-- Section 6: Conditional Addition
-- ============================================================

/-- Conditional addition: if `bit = 1`, `result = acc + P`; if `bit = 0`,
    `result = acc`. Used as a building block for scalar multiplication. -/
def ecCondAdd (params : CurveParams F) (bit : F) (acc P result : ECPoint F)
    (lambda : F) : Prop :=
  isBool bit ∧
  (bit = 0 → result = acc) ∧
  (bit = 1 → ecAddFull params acc P result lambda)

-- ============================================================
-- Section 7: Scalar Multiplication (double-and-add chain)
-- ============================================================

/-- Scalar multiplication as a chain of doublings and conditional additions.

    Processing bits from MSB to LSB:
    - `intermediates 0` = identity (point at infinity)
    - For each bit `i`: double, then conditionally add `P`
    - `intermediates n` = `scalar · P`

    The prover supplies all intermediate points and witness slopes. -/
def ecScalarMulChain (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F) : Prop :=
  -- All scalar bits are boolean
  (∀ i, isBool (scalar_bits i)) ∧
  -- Start with identity (point at infinity)
  intermediates ⟨0, by omega⟩ = ⟨0, 0, 1⟩ ∧
  -- Each step: double then conditionally add
  ∀ i : Fin n,
    -- doubled(i) = 2 · intermediate(i) OR identity if intermediate(i) is O
    ((intermediates i.castSucc).is_inf = 1 →
      doubled i = ⟨0, 0, 1⟩) ∧
    ((intermediates i.castSucc).is_inf = 0 →
      ecDoubleConstraint params (intermediates i.castSucc) (doubled i) (double_lambdas i)) ∧
    -- intermediate(i+1) = doubled(i) + bit(i) · P
    ecCondAdd params (scalar_bits i) (doubled i) P (intermediates i.succ) (add_lambdas i)

-- ============================================================
-- Section 8: Correctness Theorems
-- ============================================================

/-- Point addition preserves curve membership.

    Requires `x₁ ≠ x₂` (the precondition for general point addition).
    The proof multiplies through by `(x₁ - x₂)`, applies `linear_combination`
    with polynomial cofactors, then cancels the nonzero factor. -/
theorem ecAddConstraint_valid (params : CurveParams F) (p1 p2 p3 : ECPoint F) (lambda : F)
    (hp1 : ecPointValid params p1) (hp2 : ecPointValid params p2)
    (hadd : ecAddConstraint p1 p2 p3 lambda)
    (hne : p1.x ≠ p2.x) :
    ecPointValid params p3 := by
  obtain ⟨hinf1, hinf2, hinf3, hslope, hx3, hy3⟩ := hadd
  constructor
  · rw [hinf3]
    exact (isBool_iff _).mpr (Or.inl rfl)
  · intro _
    have hoc1 := hp1.2 hinf1
    have hoc2 := hp2.2 hinf2
    rw [hy3, hx3]
    -- Strategy: show (x₁ - x₂) * (LHS - RHS) = 0, then cancel x₁ - x₂ ≠ 0.
    have hne' : p1.x - p2.x ≠ 0 := sub_ne_zero.mpr hne
    have hmul : (p1.x - p2.x) *
        ((lambda * (p1.x - (lambda * lambda - p1.x - p2.x)) - p1.y) *
          (lambda * (p1.x - (lambda * lambda - p1.x - p2.x)) - p1.y) -
        ((lambda * lambda - p1.x - p2.x) * (lambda * lambda - p1.x - p2.x) *
          (lambda * lambda - p1.x - p2.x) +
          params.a * (lambda * lambda - p1.x - p2.x) + params.b)) = 0 := by
      linear_combination
        (2 * p1.x + p2.x - lambda * lambda) *
          (p1.y + p2.y + lambda * (p2.x - p1.x)) * hslope +
        (lambda * lambda - p1.x - 2 * p2.x) * hoc1 +
        (2 * p1.x + p2.x - lambda * lambda) * hoc2
    exact eq_of_sub_eq_zero (or_iff_not_imp_left.mp (mul_eq_zero.mp hmul) hne')

/-- Point doubling preserves curve membership.

    The algebraic identity: given `λ·(2y₁) = 3x₁²+a`, `y₁² = x₁³+ax₁+b`,
    and `x₃ = λ²-2x₁`, `y₃ = λ(x₁-x₃)-y₁`,
    we must show `y₃² = x₃³ + a·x₃ + b`. -/
theorem ecDoubleConstraint_valid (params : CurveParams F) (p1 p3 : ECPoint F) (lambda : F)
    (hp1 : ecPointValid params p1)
    (hdbl : ecDoubleConstraint params p1 p3 lambda) :
    ecPointValid params p3 := by
  obtain ⟨hinf1, hinf3, hslope, hx3, hy3⟩ := hdbl
  constructor
  · rw [hinf3]
    exact (isBool_iff _).mpr (Or.inl rfl)
  · intro _
    have hoc1 := hp1.2 hinf1
    rw [hy3, hx3]
    linear_combination
      (lambda * lambda - 3 * p1.x) * hslope + hoc1

-- ============================================================
-- Section 9: Identity cases
-- ============================================================

/-- Adding the identity point (on the left) yields the other point. -/
theorem ecAddFull_identity_left (params : CurveParams F) (p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddFull params ⟨0, 0, 1⟩ p2 p3 lambda) :
    p3 = p2 :=
  hadd.1 rfl

/-- Adding the identity point (on the right) yields the other point. -/
theorem ecAddFull_identity_right (params : CurveParams F) (p1 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddFull params p1 ⟨0, 0, 1⟩ p3 lambda) :
    p3 = p1 :=
  hadd.2.1 rfl

/-- Adding a point and its negation yields the identity. -/
theorem ecAddFull_inverse (params : CurveParams F) (p1 p2 p3 : ECPoint F) (lambda : F)
    (hadd : ecAddFull params p1 p2 p3 lambda)
    (h1 : p1.is_inf = 0) (h2 : p2.is_inf = 0)
    (hx : p1.x = p2.x) (hy : p1.y + p2.y = 0) :
    p3.is_inf = 1 :=
  hadd.2.2.1 h1 h2 hx hy

-- ============================================================
-- Section 10: Conditional add correctness
-- ============================================================

/-- Conditional add with bit = 0 is the identity. -/
theorem ecCondAdd_zero (params : CurveParams F) (acc P result : ECPoint F) (lambda : F)
    (h : ecCondAdd params 0 acc P result lambda) :
    result = acc :=
  h.2.1 rfl

/-- Conditional add with bit = 1 is full addition. -/
theorem ecCondAdd_one (params : CurveParams F) (acc P result : ECPoint F) (lambda : F)
    (h : ecCondAdd params 1 acc P result lambda) :
    ecAddFull params acc P result lambda :=
  h.2.2 rfl
