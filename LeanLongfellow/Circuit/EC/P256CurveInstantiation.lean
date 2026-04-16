import LeanLongfellow.Circuit.EC.CurveInstantiation
import LeanLongfellow.Circuit.ECDSA.Circuit
import LeanLongfellow.Circuit.EC.ScalarMul

/-! # Concrete P-256 CurveInstantiation

Provides a `CurveInstantiation F_p256` instance that bridges abstract
`EllipticCurve` operations to the concrete P-256 circuit constraint
system.  This closes the gap between the abstract ECDSA extraction
theorem (`ecdsaConstraint_implies_verify`) and concrete P-256 arithmetic.

## Main result

`instance : CurveInstantiation F_p256` — every field of the
`CurveInstantiation` class is proved for P-256, connecting circuit-level
`ECPoint`/`ecAddFull`/`ecDoubleConstraint`/`ecScalarMulChain` to the
Mathlib-backed `EllipticCurve F_p256` instance.

## Sorry audit

All fields fully proved (zero sorries).
-/

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

set_option autoImplicit false

-- ============================================================
-- Section 1: p256_toECPoint — abstract Point → circuit ECPoint
-- ============================================================

/-- Convert an abstract `Point p256WCurve` to a circuit `ECPoint F_p256`.
    - `Point.zero` (identity) maps to `⟨0, 0, 1⟩` (is_inf = 1).
    - `Point.some x y _` maps to `⟨x, y, 0⟩` (is_inf = 0). -/
noncomputable def p256_toECPoint : Point p256WCurve → ECPoint F_p256
  | Point.zero => ⟨0, 0, 1⟩
  | Point.some x y _ => ⟨x, y, 0⟩

-- ============================================================
-- Section 2: Basic lemmas about p256_toECPoint
-- ============================================================

@[simp]
theorem p256_toECPoint_zero : p256_toECPoint Point.zero = ⟨0, 0, 1⟩ := rfl

@[simp]
theorem p256_toECPoint_some {x y : F_p256} (h : Nonsingular p256WCurve x y) :
    p256_toECPoint (Point.some x y h) = ⟨x, y, 0⟩ := rfl

/-- ECPoint extensionality: two ECPoints with equal fields are equal. -/
private theorem ecpoint_ext (p q : ECPoint F_p256)
    (hx : p.x = q.x) (hy : p.y = q.y) (hinf : p.is_inf = q.is_inf) :
    p = q := by
  cases p; cases q; simp only [ECPoint.mk.injEq]; exact ⟨hx, hy, hinf⟩

-- ============================================================
-- Section 3: p256_toECPoint preserves validity
-- ============================================================

/-- The generator point as a circuit `ECPoint`. -/
noncomputable def p256GeneratorECPoint : ECPoint F_p256 :=
  p256_toECPoint p256Generator

/-- The generator `ECPoint` matches the abstract generator conversion. -/
theorem p256_generator_agree :
    p256_toECPoint (@EllipticCurve.generator F_p256 _ _) = p256GeneratorECPoint := rfl

/-- A Mathlib `Point` maps to a valid circuit `ECPoint`. -/
theorem p256_toECPoint_valid (P : Point p256WCurve) :
    ecPointValid p256CurveParams (p256_toECPoint P) := by
  cases P with
  | zero =>
    constructor
    · exact (isBool_iff _).mpr (Or.inr rfl)
    · intro h; simp [p256_toECPoint] at h
  | some x y hns =>
    constructor
    · exact (isBool_iff _).mpr (Or.inl rfl)
    · intro _
      simp only [p256_toECPoint, p256CurveParams]
      have heq := hns.1
      rw [equation_iff] at heq
      simp only [p256WCurve] at heq
      linear_combination heq

/-- The generator is a valid circuit point on P-256. -/
theorem p256_generatorECPoint_valid :
    ecPointValid p256CurveParams p256GeneratorECPoint :=
  p256_toECPoint_valid p256Generator

-- ============================================================
-- Section 4: Round-trip lemma
-- ============================================================

/-- Converting an abstract point to circuit format and back recovers
    the original point. -/
theorem p256_toECPoint_roundtrip (P : Point p256WCurve) :
    ECPoint.toP256Point (p256_toECPoint P) (p256_toECPoint_valid P) = P := by
  cases P with
  | zero =>
    show ECPoint.toP256Point ⟨0, 0, 1⟩ _ = Point.zero
    exact ECPoint.toP256Point_zero ⟨0, 0, 1⟩ _ rfl
  | some x y hns =>
    show ECPoint.toP256Point ⟨x, y, 0⟩ _ = Point.some x y hns
    rw [ECPoint.toP256Point_some _ _ rfl]

-- ============================================================
-- Section 5: xCoord agreement
-- ============================================================

theorem p256_xCoord_agree (P : Point p256WCurve) :
    @EllipticCurve.xCoord F_p256 _ _ P = (p256_toECPoint P).x := by
  cases P with
  | zero => rfl
  | some x y _ => rfl

-- ============================================================
-- Section 6: nonIdentity_is_fin
-- ============================================================

theorem p256_nonIdentity_is_fin (P : Point p256WCurve)
    (hne : P ≠ @EllipticCurve.identity F_p256 _ _) :
    (p256_toECPoint P).is_inf = 0 := by
  cases P with
  | zero => exact absurd rfl hne
  | some x y _ => rfl

-- ============================================================
-- Section 7: Auxiliary — y₁ = y₂ or y₁ = -y₂ when x₁ = x₂
-- ============================================================

/-- On P-256, two points with the same x-coordinate satisfy
    y₁ = y₂ or y₁ + y₂ = 0. -/
private theorem p256_y_eq_or_neg {x₁ y₁ x₂ y₂ : F_p256}
    (h₁ : Nonsingular p256WCurve x₁ y₁)
    (h₂ : Nonsingular p256WCurve x₂ y₂)
    (hx : x₁ = x₂) :
    y₁ = y₂ ∨ y₁ + y₂ = 0 := by
  subst hx
  have heq1 := h₁.1
  have heq2 := h₂.1
  rw [equation_iff] at heq1 heq2
  simp only [p256WCurve] at heq1 heq2
  -- y₁² = y₂² (same x on same curve)
  have hysq : y₁ ^ 2 = y₂ ^ 2 := by linear_combination heq1 - heq2
  -- (y₁ - y₂)(y₁ + y₂) = y₁² - y₂² = 0
  have hfact : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination hysq
  rcases mul_eq_zero.mp hfact with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact h

-- ============================================================
-- Section 8: No order-2 points on P-256
-- ============================================================

/-- On P-256, `ecDoubleConstraint` cannot hold when `2y₁ = 0` for a
    point that is on the curve.  The proof derives `b² = 4` in `F_p256`
    (where `b` is the P-256 `b` constant), then refutes by `native_decide`. -/
private theorem p256_2y_ne_zero_of_doubleConstraint
    {x₁ y₁ : F_p256}
    (hv : ecPointValid p256CurveParams ⟨x₁, y₁, (0 : F_p256)⟩)
    {d : ECPoint F_p256} {lam : F_p256}
    (hdbl : ecDoubleConstraint p256CurveParams ⟨x₁, y₁, (0 : F_p256)⟩ d lam) :
    y₁ + y₁ ≠ 0 := by
  intro h2y
  -- char p256 > 2, so 2y = 0 implies y = 0
  have h2ne : (2 : F_p256) ≠ 0 := by native_decide
  have hy0 : y₁ = 0 := by
    have h2y' : (2 : F_p256) * y₁ = 0 := by linear_combination h2y
    exact (mul_eq_zero.mp h2y').resolve_left h2ne
  -- Slope constraint: lam * (2y₁) = 3x₁² + a, with y₁ = 0 gives 0 = 3x₁² + (-3)
  have hslope := hdbl.2.2.1
  simp only [p256CurveParams] at hslope
  rw [hy0] at hslope
  simp only [mul_zero] at hslope
  -- hslope : 0 = 3 * x₁ * x₁ + (-3 : F_p256)
  -- So 3x₁² = 3, hence x₁² = 1
  have h3ne : (3 : F_p256) ≠ 0 := by native_decide
  have hx2 : x₁ * x₁ = 1 := by
    have h3eq : (3 : F_p256) * (x₁ * x₁) = 3 * 1 := by linear_combination -hslope
    rw [mul_one] at h3eq
    exact mul_left_cancel₀ h3ne h3eq
  -- On-curve: y₁² = x₁³ + ax₁ + b, with y₁ = 0 gives 0 = x₁³ - 3x₁ + b
  have hoc := hv.2 rfl
  simp only [p256CurveParams] at hoc
  rw [hy0, zero_mul] at hoc
  -- hoc : 0 = x₁ * x₁ * x₁ + (-3) * x₁ + ↑p256_b
  -- x₁³ = x₁ * (x₁²) = x₁ * 1 = x₁
  have hx3 : x₁ * x₁ * x₁ = x₁ := by
    rw [mul_assoc, hx2, mul_one]
  rw [hx3] at hoc
  -- hoc : 0 = x₁ + (-3) * x₁ + ↑p256_b = -2x₁ + b
  -- So 2x₁ = b. Rearrange algebraically.
  have hx_eq : (2 : F_p256) * x₁ = (p256_b : F_p256) := by
    have h : x₁ + (-3 : F_p256) * x₁ + (p256_b : F_p256) = 0 := by
      linear_combination -hoc
    -- x₁ + (-3)*x₁ = -2*x₁
    have h' : (-2 : F_p256) * x₁ + (p256_b : F_p256) = 0 := by linear_combination h
    -- So b = 2x₁
    linear_combination -h'
  -- x₁ = b * 2⁻¹
  have hx_val : x₁ = (p256_b : F_p256) * (2 : F_p256)⁻¹ := by
    have := congr_arg (· * (2 : F_p256)⁻¹) hx_eq
    simp only [mul_comm (2 : F_p256) x₁, mul_assoc, mul_inv_cancel₀ h2ne, mul_one] at this
    exact this
  -- x₁² = 1 with x₁ = b/2 gives (b/2)² = 1
  rw [hx_val] at hx2
  -- hx2 : b * 2⁻¹ * (b * 2⁻¹) = 1
  -- Multiply both sides by 4 = 2 * 2 to get b² = 4
  have h4 : (p256_b : F_p256) * (p256_b : F_p256) = 4 := by
    have hmul : (p256_b : F_p256) * (p256_b : F_p256) *
        ((2 : F_p256)⁻¹ * (2 : F_p256)⁻¹) = 1 := by ring_nf; exact hx2
    have h2inv_ne : (2 : F_p256)⁻¹ ≠ 0 := inv_ne_zero h2ne
    have h22_ne : (2 : F_p256)⁻¹ * (2 : F_p256)⁻¹ ≠ 0 := mul_ne_zero h2inv_ne h2inv_ne
    have h4eq : (4 : F_p256) * ((2 : F_p256)⁻¹ * (2 : F_p256)⁻¹) = 1 := by
      show (2 * 2 : F_p256) * ((2 : F_p256)⁻¹ * (2 : F_p256)⁻¹) = 1
      rw [mul_assoc, ← mul_assoc (2 : F_p256) ((2 : F_p256)⁻¹),
          mul_inv_cancel₀ h2ne, one_mul, mul_inv_cancel₀ h2ne]
    exact mul_right_cancel₀ h22_ne (hmul.trans h4eq.symm)
  -- b² ≠ 4 on P-256
  exact absurd h4 (by native_decide)

-- ============================================================
-- Section 9: doublePoint_agree
-- ============================================================

/-- Circuit doubling on P-256 matches abstract point doubling. -/
theorem p256_doublePoint_agree (P : Point p256WCurve)
    (d : ECPoint F_p256) (lam : F_p256)
    (hfin : (p256_toECPoint P).is_inf = 0)
    (hdbl : ecDoubleConstraint p256CurveParams (p256_toECPoint P) d lam) :
    d = p256_toECPoint (@EllipticCurve.pointAdd F_p256 _ _ P P) := by
  cases P with
  | zero => simp [p256_toECPoint] at hfin
  | some x₁ y₁ h₁ =>
    simp only [p256_toECPoint] at hfin hdbl ⊢
    have hv1 : ecPointValid p256CurveParams ⟨x₁, y₁, (0 : F_p256)⟩ :=
      p256_toECPoint_valid (Point.some x₁ y₁ h₁)
    have hvd : ecPointValid p256CurveParams d :=
      ecDoubleConstraint_valid p256CurveParams ⟨x₁, y₁, 0⟩ d lam hv1 hdbl
    -- Prove 2y₁ ≠ 0
    have hny : y₁ + y₁ ≠ 0 := p256_2y_ne_zero_of_doubleConstraint hv1 hdbl
    -- Standard doubling case
    have hcorrect := p256_ecDouble_correct ⟨x₁, y₁, 0⟩ d lam hv1 hvd hdbl hny
    rw [ECPoint.toP256Point_some _ hv1 rfl] at hcorrect
    have hinfd := hdbl.2.1
    rw [ECPoint.toP256Point_some d hvd hinfd] at hcorrect
    -- y₁ ≠ negY (short Weierstrass negY = -y)
    have hy_neg : y₁ ≠ negY p256WCurve x₁ y₁ := by
      rw [← p256_params_match, shortWeierstrass_negY]
      intro heq
      exact hny (by linear_combination heq)
    show d = p256_toECPoint (Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁)
    rw [add_self_of_Y_ne hy_neg, p256_toECPoint_some]
    rw [add_self_of_Y_ne hy_neg] at hcorrect
    exact ecpoint_ext d _ (some.inj hcorrect).left (some.inj hcorrect).right hinfd

-- ============================================================
-- Section 10: pointAdd_agree
-- ============================================================

/-- Circuit full addition on P-256 agrees with abstract point addition.

    Five cases by structure of P, Q, and coordinate equality:
    P=O, Q=O, same-x-same-y (doubling), same-x-neg-y (inverse), different-x. -/
theorem p256_pointAdd_agree (P Q : Point p256WCurve)
    (p3 : ECPoint F_p256) (lam : F_p256)
    (hadd : ecAddFull p256CurveParams (p256_toECPoint P) (p256_toECPoint Q) p3 lam) :
    p3 = p256_toECPoint (@EllipticCurve.pointAdd F_p256 _ _ P Q) := by
  cases P with
  | zero =>
    -- P = O: result = Q
    change p3 = p256_toECPoint ((0 : Point p256WCurve) + Q)
    rw [_root_.zero_add]
    exact hadd.1 rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change p3 = p256_toECPoint (Point.some x₁ y₁ h₁ + (0 : Point p256WCurve))
      rw [_root_.add_zero]
      exact hadd.2.1 rfl
    | some x₂ y₂ h₂ =>
      simp only [p256_toECPoint] at hadd
      show p3 = p256_toECPoint (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂)
      by_cases hx : x₁ = x₂
      · -- x₁ = x₂
        rcases p256_y_eq_or_neg h₁ h₂ hx with hys | hyneg
        · -- y₁ = y₂: doubling case
          have hdbl := hadd.2.2.2.1 rfl rfl hx hys
          have hdbl' : ecDoubleConstraint p256CurveParams
              (p256_toECPoint (Point.some x₁ y₁ h₁)) p3 lam := by
            simp only [p256_toECPoint]; exact hdbl
          have hd := p256_doublePoint_agree (Point.some x₁ y₁ h₁) p3 lam rfl hdbl'
          -- Since x₁ = x₂ and y₁ = y₂, the sums agree
          rw [hd]; congr 1; subst hx; subst hys; rfl
        · -- y₁ + y₂ = 0: inverse case, P + Q = O
          have hy_neg : y₁ = negY p256WCurve x₂ y₂ := by
            rw [← p256_params_match, shortWeierstrass_negY]
            linear_combination hyneg
          rw [add_of_Y_eq hx hy_neg]
          -- ecAddFull now gives p3 = ⟨0, 0, 1⟩ in the inverse case
          exact hadd.2.2.1 rfl rfl hx hyneg
      · -- x₁ ≠ x₂: general addition
        have hadd_c := hadd.2.2.2.2 rfl rfl hx
        have hv1 : ecPointValid p256CurveParams ⟨x₁, y₁, 0⟩ :=
          p256_toECPoint_valid (Point.some x₁ y₁ h₁)
        have hv2 : ecPointValid p256CurveParams ⟨x₂, y₂, 0⟩ :=
          p256_toECPoint_valid (Point.some x₂ y₂ h₂)
        have hv3 : ecPointValid p256CurveParams p3 :=
          ecAddConstraint_valid p256CurveParams ⟨x₁, y₁, 0⟩ ⟨x₂, y₂, 0⟩ p3 lam
            hv1 hv2 hadd_c hx
        have hcorrect := p256_ecAdd_correct ⟨x₁, y₁, 0⟩ ⟨x₂, y₂, 0⟩ p3 lam
          hv1 hv2 hv3 hadd_c hx
        rw [ECPoint.toP256Point_some _ hv1 rfl,
            ECPoint.toP256Point_some _ hv2 rfl] at hcorrect
        have hinf3 := hadd_c.2.2.1
        rw [ECPoint.toP256Point_some p3 hv3 hinf3] at hcorrect
        rw [add_of_X_ne hx] at hcorrect ⊢
        rw [p256_toECPoint_some]
        exact ecpoint_ext p3 _ (some.inj hcorrect).left (some.inj hcorrect).right hinf3

-- ============================================================
-- Section 11: doubleAndAdd = nsmul for P-256
-- ============================================================

/-- On P-256, `EllipticCurve.pointAdd` is `(· + ·)` on `Point p256WCurve`. -/
private theorem p256_pointAdd_eq_add (A B : Point p256WCurve) :
    @EllipticCurve.pointAdd F_p256 _ _ A B = A + B := rfl

/-- On P-256, `EllipticCurve.identity` is `0 : Point p256WCurve`. -/
private theorem p256_identity_eq_zero :
    @EllipticCurve.identity F_p256 _ _ = (0 : Point p256WCurve) := rfl

/-- On P-256, `doubleAndAdd n bits P = (bitsToNat n bits) • P`.
    Proved directly by induction, avoiding `EllipticCurveGroup`/`nsmulEC`. -/
private theorem p256_doubleAndAdd_eq_nsmul (n : ℕ) (bits : Fin n → Bool)
    (P : Point p256WCurve) :
    doubleAndAdd (F := F_p256) n bits P = (bitsToNat n bits) • P := by
  induction n with
  | zero =>
    rw [doubleAndAdd_zero, bitsToNat_zero, p256_identity_eq_zero]
    exact (zero_smul ℕ P).symm
  | succ n ih =>
    rw [doubleAndAdd_succ, bitsToNat_succ]
    set acc := doubleAndAdd (F := F_p256) n (fun i => bits ⟨i.val, by omega⟩) P
    have ih_val := ih (fun i => bits ⟨i.val, by omega⟩)
    set k := bitsToNat n (fun i => bits ⟨i.val, by omega⟩)
    -- Doubling: pointAdd acc acc = 2k • P
    have hacc : acc = k • P := ih_val
    have hdbl : @EllipticCurve.pointAdd F_p256 _ _ acc acc = (2 * k) • P := by
      rw [p256_pointAdd_eq_add, hacc, two_mul, add_nsmul]
    -- Split on the bit
    by_cases hb : bits ⟨n, by omega⟩
    · simp only [hb, ite_true]
      -- Goal: pointAdd (pointAdd acc acc) P = (2k + 1) • P
      rw [p256_pointAdd_eq_add, hdbl, add_nsmul, one_nsmul, add_comm]
    · simp only [hb]
      exact hdbl

-- ============================================================
-- Section 13: bitsToNat bound
-- ============================================================

/-- `bitsToNat n bits < 2 ^ n` for any boolean bit vector. -/
private theorem bitsToNat_lt_pow (n : ℕ) (bits : Fin n → Bool) :
    bitsToNat n bits < 2 ^ n := by
  induction n with
  | zero => simp [bitsToNat_zero]
  | succ n ih =>
    rw [bitsToNat_succ, Nat.pow_succ]
    have h_sub := ih (fun i => bits ⟨i.val, by omega⟩)
    by_cases hb : bits ⟨n, by omega⟩
    · simp [hb]; omega
    · simp [hb]; omega

-- ============================================================
-- Section 14: Field sum = bitsToNat cast to field
-- ============================================================

/-- The Horner-form natural number `bitsToNat` equals the MSB-first
    Finset sum when both are computed over booleans. -/
private theorem bitsToNat_eq_finset_sum (n : ℕ) (bits_bool : Fin n → Bool) :
    (bitsToNat n bits_bool : ℕ) =
      ∑ i : Fin n, (if bits_bool i then 1 else 0) * 2 ^ (n - 1 - (i : ℕ)) := by
  induction n with
  | zero => simp [bitsToNat_zero]
  | succ n ih =>
    rw [bitsToNat_succ]
    have ih' := ih (fun i => bits_bool ⟨i.val, by omega⟩)
    rw [Fin.sum_univ_castSucc]
    -- Work with the prefix sum: rewrite castSucc → val
    have hpfx : (∑ i : Fin n,
        (if bits_bool (Fin.castSucc i) then 1 else 0) *
          2 ^ (n + 1 - 1 - (Fin.castSucc i : ℕ))) =
        2 * (bitsToNat n fun i => bits_bool ⟨↑i, by omega⟩) := by
      rw [ih', Finset.mul_sum]
      congr 1; funext i
      have hcs : Fin.castSucc i = (⟨↑i, by omega⟩ : Fin (n + 1)) := by
        ext; simp [Fin.val_castSucc]
      rw [hcs, show n + 1 - 1 - (i : ℕ) = (n - 1 - (i : ℕ)) + 1 by omega]
      rw [pow_succ]; ring
    rw [hpfx]
    -- Last term
    have hlast : Fin.last n = (⟨n, by omega⟩ : Fin (n + 1)) := by
      ext; simp [Fin.val_last]
    rw [hlast, show n + 1 - 1 - n = 0 by omega, pow_zero, Nat.mul_one]

/-- When bits are boolean field elements matching a bool vector, the field
    sum `∑ bits[i] * 2^(n-1-i)` equals `(bitsToNat n bits_bool : F_p256)`. -/
private theorem field_sum_eq_bitsToNat_cast (n : ℕ) (bits : Fin n → F_p256)
    (bits_bool : Fin n → Bool)
    (hbits : ∀ i : Fin n, bits i = if bits_bool i then (1 : F_p256) else 0) :
    (∑ i : Fin n, bits i * (2 : F_p256) ^ (n - 1 - (i : ℕ))) =
      (bitsToNat n bits_bool : F_p256) := by
  -- Rewrite bits to their bool form
  have hrw : ∀ i : Fin n, bits i * (2 : F_p256) ^ (n - 1 - (i : ℕ)) =
      (if bits_bool i then (1 : F_p256) else 0) * (2 : F_p256) ^ (n - 1 - (i : ℕ)) :=
    fun i => by rw [hbits i]
  rw [Finset.sum_congr rfl (fun i _ => hrw i)]
  -- Cast bitsToNat to F_p256 and show the sums agree
  rw [bitsToNat_eq_finset_sum n bits_bool]
  push_cast [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hb : bits_bool i <;> simp [hb]

-- ============================================================
-- Section 15: bitsToNat = ZMod.val scalar (the number theory bridge)
-- ============================================================

/-- If `isBitDecomp bits scalar` and `2^n ≤ p256Prime`, then
    `bitsToNat n bits_bool = ZMod.val scalar`. -/
private theorem bitsToNat_eq_val (n : ℕ) (bits : Fin n → F_p256) (scalar : F_p256)
    (hdecomp : isBitDecomp bits scalar)
    (bits_bool : Fin n → Bool)
    (hbits : ∀ i : Fin n, bits i = if bits_bool i then (1 : F_p256) else 0)
    (hn : 2 ^ n ≤ Fintype.card F_p256) :
    bitsToNat n bits_bool = ZMod.val scalar := by
  -- scalar = ∑ bits[i] * 2^(n-1-i) in F_p256
  have hsum := hdecomp.2
  -- ∑ bits[i] * 2^(n-1-i) = (bitsToNat : F_p256)
  have hfield := field_sum_eq_bitsToNat_cast n bits bits_bool hbits
  -- Therefore scalar = (bitsToNat : F_p256)
  have hscalar : scalar = (bitsToNat n bits_bool : F_p256) := by
    rw [hsum, hfield]
  -- bitsToNat < 2^n ≤ p256Prime = Fintype.card F_p256
  have hlt : bitsToNat n bits_bool < Fintype.card F_p256 := by
    calc bitsToNat n bits_bool < 2 ^ n := bitsToNat_lt_pow n bits_bool
    _ ≤ Fintype.card F_p256 := hn
  -- Since Fintype.card F_p256 = p256Prime > 0
  have hcard : Fintype.card F_p256 = p256Prime := ZMod.card p256Prime
  rw [hcard] at hlt
  -- ZMod.val (↑m) = m when m < p
  rw [hscalar]
  exact (ZMod.val_natCast_of_lt hlt).symm

-- ============================================================
-- Section 16: scalarMul_agree
-- ============================================================

/-- **Scalar multiplication agreement for P-256.**

    Given a valid bit decomposition and scalar multiplication chain,
    the chain's final point matches the abstract scalar multiplication
    `(ZMod.val scalar) • P`.

    Proof outline:
    1. `scalarMulChain_invariant_explicit` shows the chain computes
       `doubleAndAdd n bits_bool P`.
    2. `p256_doubleAndAdd_eq_nsmul` shows `doubleAndAdd = (bitsToNat ...) • P`.
    3. `bitsToNat_eq_val` shows `bitsToNat = ZMod.val scalar` when
       `2^n ≤ Fintype.card F_p256`.
    4. `scalarMul scalar P = (ZMod.val scalar) • P` by definition. -/
theorem p256_scalarMul_agree
    (scalar : F_p256) (P : Point p256WCurve) (n : ℕ)
    (bits : Fin n → F_p256) (ints : Fin (n + 1) → ECPoint F_p256)
    (dbl : Fin n → ECPoint F_p256) (dl al : Fin n → F_p256)
    (hn : 2 ^ n ≤ Fintype.card F_p256)
    (hdecomp : isBitDecomp bits scalar)
    (hchain : ecScalarMulChain p256CurveParams n bits (p256_toECPoint P) ints dbl dl al) :
    ints ⟨n, by omega⟩ = p256_toECPoint ((ZMod.val scalar) • P) := by
  -- Convert field bits to booleans
  set bits_bool := chainBitsToBool n bits (hchain.1) with hbb_def
  have hbits_agree : ∀ i : Fin n,
      bits i = if bits_bool i then (1 : F_p256) else 0 :=
    fun i => chainBitsToBool_agree n bits hchain.1 i
  -- Step 1: chain computes doubleAndAdd
  have h_chain := scalarMulChain_invariant_explicit
    p256CurveParams
    p256_toECPoint
    rfl       -- identity_toECPoint
    rfl       -- identity_agree
    p256_nonIdentity_is_fin
    p256_doublePoint_agree
    p256_pointAdd_agree
    n bits (p256_toECPoint P) P rfl
    ints dbl dl al hchain
    bits_bool hbits_agree
    n (le_refl n)
  simp only [Fin.eta] at h_chain
  -- Step 2: doubleAndAdd = (bitsToNat ...) • P
  have h_da := p256_doubleAndAdd_eq_nsmul n bits_bool P
  -- Step 3: bitsToNat = ZMod.val scalar
  have h_val := bitsToNat_eq_val n bits scalar hdecomp bits_bool hbits_agree hn
  -- Combine: ints = toECPoint (doubleAndAdd ...) = toECPoint (bitsToNat • P)
  --   = toECPoint (ZMod.val scalar • P) = toECPoint (scalarMul scalar P)
  -- EllipticCurve.scalarMul (fieldToNat scalar) P = (ZMod.val scalar) • P by definition
  -- (fieldToNat = ZMod.val, scalarMul n P = n • P)
  show ints ⟨n, by omega⟩ = p256_toECPoint ((ZMod.val scalar) • P)
  rw [h_chain, h_da, h_val]

-- ============================================================
-- Section 17: The CurveInstantiation instance
-- ============================================================

/-- **Concrete P-256 CurveInstantiation.**

    Connects the abstract `EllipticCurve F_p256` instance to the concrete
    circuit constraint system. All fields fully proved (zero sorries). -/
noncomputable instance : CurveInstantiation F_p256 where
  params := p256CurveParams
  generatorPoint := p256GeneratorECPoint
  generatorValid := p256_generatorECPoint_valid
  toECPoint := p256_toECPoint
  xCoord_agree := p256_xCoord_agree
  generator_agree := p256_generator_agree
  scalarMul_agree := p256_scalarMul_agree
  pointAdd_agree := p256_pointAdd_agree
  identity_agree := rfl
  identity_toECPoint := rfl
  nonIdentity_is_fin := p256_nonIdentity_is_fin
  doublePoint_agree := p256_doublePoint_agree
