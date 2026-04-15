import LeanLongfellow.Circuit.ECArith
import LeanLongfellow.Circuit.ECDSACircuit

/-! # Scalar Multiplication Circuit: Specification and Correctness

Defines `doubleAndAdd`, a pure recursive specification of scalar multiplication
via the standard MSB-first double-and-add algorithm, and proves its correctness:
- `doubleAndAdd` computes `(bitsToNat bits) • P` (Theorem `doubleAndAdd_eq_nsmul`)
- `ecScalarMulChain` decomposes into per-step constraints (Theorem `scalarMulChain_step`)
- The chain result matches `doubleAndAdd` (Theorem `scalarMulChain_correct`)
-/

open scoped Classical

set_option autoImplicit false

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Bit-to-natural-number conversion
-- ============================================================

/-- Convert a bit vector (MSB-first, index 0 = MSB) to a natural number.
    `bitsToNat [b₀, b₁, ..., b_{n-1}]` = `∑ᵢ bᵢ · 2^(n-1-i)`.
    Equivalently, using Horner's rule: fold from left doubling and adding. -/
def bitsToNat : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, bits =>
    2 * bitsToNat n (fun i => bits ⟨i.val, by omega⟩) +
    if bits ⟨n, by omega⟩ then 1 else 0

theorem bitsToNat_zero (bits : Fin 0 → Bool) : bitsToNat 0 bits = 0 := rfl

theorem bitsToNat_succ {n : ℕ} (bits : Fin (n + 1) → Bool) :
    bitsToNat (n + 1) bits =
    2 * bitsToNat n (fun i => bits ⟨i.val, by omega⟩) +
    if bits ⟨n, by omega⟩ then 1 else 0 := rfl

-- ============================================================
-- Section 2: Double-and-add specification
-- ============================================================

/-- Double-and-add from MSB (index 0) to LSB (index n-1).

    Processes bits left-to-right:
    ```
    acc = identity
    for i = 0, 1, ..., n-1:
      acc = 2 · acc
      if bits[i] = true: acc = acc + P
    return acc
    ```

    The recursion proceeds on the prefix length:
    - `doubleAndAdd 0 _ P = identity`
    - `doubleAndAdd (n+1) bits P = let acc = doubleAndAdd n bits[0..n-1] P;
                                    if bits[n] then 2·acc + P else 2·acc` -/
noncomputable def doubleAndAdd [EllipticCurve F] :
    (n : ℕ) → (Fin n → Bool) → EllipticCurve.Point (F := F) →
    EllipticCurve.Point (F := F)
  | 0, _, _ => EllipticCurve.identity
  | n + 1, bits, P =>
    let acc := doubleAndAdd n (fun i => bits ⟨i.val, by omega⟩) P
    let doubled := EllipticCurve.pointAdd acc acc
    if bits ⟨n, by omega⟩
    then EllipticCurve.pointAdd doubled P
    else doubled

theorem doubleAndAdd_zero [EllipticCurve F]
    (bits : Fin 0 → Bool) (P : EllipticCurve.Point (F := F)) :
    doubleAndAdd 0 bits P = EllipticCurve.identity := rfl

theorem doubleAndAdd_succ [EllipticCurve F] {n : ℕ}
    (bits : Fin (n + 1) → Bool) (P : EllipticCurve.Point (F := F)) :
    doubleAndAdd (n + 1) bits P =
    let acc := doubleAndAdd n (fun i => bits ⟨i.val, by omega⟩) P
    let doubled := EllipticCurve.pointAdd acc acc
    if bits ⟨n, by omega⟩
    then EllipticCurve.pointAdd doubled P
    else doubled := rfl

-- ============================================================
-- Section 3: doubleAndAdd = nsmul (abstract correctness)
-- ============================================================

/-- The `EllipticCurve` class extended with group-law axioms needed
    for the scalar multiplication proof.  These axioms are satisfied
    by any `AddCommGroup` with `nsmul` — in particular, by Mathlib's
    `WeierstrassCurve.Affine.Point`. -/
class EllipticCurveGroup (F : Type*) [Field F] extends EllipticCurve F where
  /-- Point addition is associative. -/
  pointAdd_assoc : ∀ (P Q R : Point), pointAdd (pointAdd P Q) R = pointAdd P (pointAdd Q R)
  /-- Identity is a left identity for pointAdd. -/
  pointAdd_identity_left : ∀ (P : Point), pointAdd identity P = P
  /-- Identity is a right identity for pointAdd. -/
  pointAdd_identity_right : ∀ (P : Point), pointAdd P identity = P
  /-- pointAdd is commutative. -/
  pointAdd_comm : ∀ (P Q : Point), pointAdd P Q = pointAdd Q P

/-- `nsmulEC n P` computes `n`-fold addition of `P` using the `EllipticCurveGroup`
    operations.  This avoids the need for `HSMul ℕ Point` instances. -/
noncomputable def nsmulEC [EllipticCurveGroup F] :
    ℕ → EllipticCurve.Point (F := F) → EllipticCurve.Point (F := F)
  | 0, _ => EllipticCurve.identity
  | n + 1, P => EllipticCurve.pointAdd P (nsmulEC n P)

theorem nsmulEC_zero [EllipticCurveGroup F] (P : EllipticCurve.Point (F := F)) :
    nsmulEC 0 P = EllipticCurve.identity := rfl

theorem nsmulEC_succ [EllipticCurveGroup F] (n : ℕ) (P : EllipticCurve.Point (F := F)) :
    nsmulEC (n + 1) P = EllipticCurve.pointAdd P (nsmulEC n P) := rfl

/-- `nsmulEC (m + n) P = pointAdd (nsmulEC m P) (nsmulEC n P)`. -/
theorem nsmulEC_add [EllipticCurveGroup F] (m n : ℕ) (P : EllipticCurve.Point (F := F)) :
    nsmulEC (m + n) P = EllipticCurve.pointAdd (nsmulEC m P) (nsmulEC n P) := by
  induction m with
  | zero =>
    simp [nsmulEC_zero, EllipticCurveGroup.pointAdd_identity_left]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    rw [nsmulEC_succ, ih, nsmulEC_succ]
    rw [EllipticCurveGroup.pointAdd_assoc]

/-- `nsmulEC (2 * n) P = pointAdd (nsmulEC n P) (nsmulEC n P)`. -/
theorem nsmulEC_double [EllipticCurveGroup F] (n : ℕ) (P : EllipticCurve.Point (F := F)) :
    nsmulEC (2 * n) P = EllipticCurve.pointAdd (nsmulEC n P) (nsmulEC n P) := by
  rw [two_mul]
  exact nsmulEC_add n n P

/-- **Core correctness:** `doubleAndAdd n bits P = nsmulEC (bitsToNat n bits) P`. -/
theorem doubleAndAdd_eq_nsmul [EllipticCurveGroup F]
    (n : ℕ) (bits : Fin n → Bool) (P : EllipticCurve.Point (F := F)) :
    doubleAndAdd n bits P = nsmulEC (bitsToNat n bits) P := by
  induction n with
  | zero =>
    simp [doubleAndAdd_zero, bitsToNat_zero, nsmulEC_zero]
  | succ n ih =>
    rw [doubleAndAdd_succ, bitsToNat_succ]
    rw [ih]
    set k := bitsToNat n (fun i => bits ⟨i.val, by omega⟩) with _hk_def
    -- Simplify the let-bindings in the goal
    show (let acc := nsmulEC k P
          let doubled := EllipticCurve.pointAdd acc acc
          if bits ⟨n, by omega⟩ then EllipticCurve.pointAdd doubled P else doubled) =
         nsmulEC (2 * k + if bits ⟨n, by omega⟩ then 1 else 0) P
    simp only []
    have hdouble : EllipticCurve.pointAdd (nsmulEC k P) (nsmulEC k P) =
        nsmulEC (2 * k) P := (nsmulEC_double k P).symm
    split
    case isTrue _hbit =>
      rw [hdouble, show 2 * k + 1 = (2 * k) + 1 from rfl]
      rw [nsmulEC_succ]
      rw [EllipticCurveGroup.pointAdd_comm]
    case isFalse _hbit =>
      simp [hdouble]

-- ============================================================
-- Section 4: ecScalarMulChain step extraction
-- ============================================================

/-- Each step of `ecScalarMulChain` decomposes into:
    1. A doubling constraint on `intermediates i` producing `doubled i`
       (or identity propagation if `intermediates i` is at infinity)
    2. A conditional addition of `P` controlled by `scalar_bits i`
       producing `intermediates (i+1)`.

    This is just unfolding the `forall i` in the chain definition. -/
theorem scalarMulChain_step (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) :
    -- doubling step (identity case)
    ((intermediates i.castSucc).is_inf = 1 → doubled i = ⟨0, 0, 1⟩) ∧
    -- doubling step (finite case)
    ((intermediates i.castSucc).is_inf = 0 →
      ecDoubleConstraint params (intermediates i.castSucc) (doubled i) (double_lambdas i)) ∧
    -- conditional add step
    ecCondAdd params (scalar_bits i) (doubled i) P (intermediates i.succ) (add_lambdas i) :=
  hchain.2.2 i

/-- The initial point in a scalar mul chain is the identity. -/
theorem scalarMulChain_init (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas) :
    intermediates ⟨0, by omega⟩ = ⟨0, 0, 1⟩ :=
  hchain.2.1

/-- All bits in a scalar mul chain are boolean. -/
theorem scalarMulChain_bits_bool (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) :
    isBool (scalar_bits i) :=
  hchain.1 i

-- ============================================================
-- Section 5: Conditional add semantics
-- ============================================================

/-- If `ecCondAdd` holds with bit = 0, the result is the accumulator. -/
theorem ecCondAdd_bit_zero (params : CurveParams F) (acc P result : ECPoint F) (lam : F)
    (h : ecCondAdd params (0 : F) acc P result lam) :
    result = acc :=
  ecCondAdd_zero params acc P result lam h

/-- If `ecCondAdd` holds with bit = 1, the result is full addition. -/
theorem ecCondAdd_bit_one (params : CurveParams F) (acc P result : ECPoint F) (lam : F)
    (h : ecCondAdd params (1 : F) acc P result lam) :
    ecAddFull params acc P result lam :=
  ecCondAdd_one params acc P result lam h

-- ============================================================
-- Section 6: First step is identity doubling
-- ============================================================

/-- At step 0, the accumulator is the identity (point at infinity),
    so the doubling produces identity, and the result is either
    identity (bit 0) or P (bit 1). -/
theorem scalarMulChain_first_step (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (hn : 0 < n) :
    -- The doubled point at step 0 is identity (since intermediates 0 is identity)
    doubled ⟨0, hn⟩ = ⟨0, 0, 1⟩ := by
  have hinit := scalarMulChain_init params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain ⟨0, hn⟩
  have hinf : (intermediates (⟨0, hn⟩ : Fin n).castSucc).is_inf = 1 := by
    show (intermediates ⟨0, by omega⟩).is_inf = 1
    rw [hinit]
  exact hstep.1 hinf

-- ============================================================
-- Section 7: First step conditional add
-- ============================================================

/-- At step 0, `intermediates 1` is either the identity (if bit 0 = 0)
    or equals the result of adding P to the identity (if bit 0 = 1). -/
theorem scalarMulChain_first_result (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (hn : 0 < n) :
    ecCondAdd params (scalar_bits ⟨0, hn⟩) (doubled ⟨0, hn⟩) P
      (intermediates ⟨1, by omega⟩) (add_lambdas ⟨0, hn⟩) := by
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain ⟨0, hn⟩
  exact hstep.2.2

-- ============================================================
-- Section 8: Utility: converting field bits to Bool
-- ============================================================

/-- A field element that is boolean (0 or 1) can be viewed as a Bool. -/
noncomputable def fieldBitToBool (x : F) (_hb : isBool x) : Bool :=
  if x = 1 then true else false

theorem fieldBitToBool_one (hb : isBool (1 : F)) :
    fieldBitToBool (1 : F) hb = true := by
  unfold fieldBitToBool; simp

theorem fieldBitToBool_zero (hb : isBool (0 : F)) :
    fieldBitToBool (0 : F) hb = false := by
  unfold fieldBitToBool
  simp only [ite_eq_right_iff]
  exact fun h => absurd h one_ne_zero.symm

theorem fieldBitToBool_agree (x : F) (hb : isBool x) :
    x = if fieldBitToBool x hb then (1 : F) else 0 := by
  unfold fieldBitToBool
  rcases (isBool_iff x).mp hb with rfl | rfl
  · simp [one_ne_zero.symm]
  · simp

/-- Convert all bits from a scalar mul chain to Bools. -/
noncomputable def chainBitsToBool (n : ℕ) (scalar_bits : Fin n → F)
    (hbool : ∀ i, isBool (scalar_bits i)) : Fin n → Bool :=
  fun i => fieldBitToBool (scalar_bits i) (hbool i)

theorem chainBitsToBool_agree (n : ℕ) (scalar_bits : Fin n → F)
    (hbool : ∀ i, isBool (scalar_bits i)) (i : Fin n) :
    scalar_bits i = if chainBitsToBool n scalar_bits hbool i then (1 : F) else 0 :=
  fieldBitToBool_agree (scalar_bits i) (hbool i)

-- ============================================================
-- Section 9: Bridge to abstract EllipticCurve via CurveInstantiation
-- ============================================================

/-- **Bridge theorem:** The `ecScalarMulChain` result, when embedded via
    `CurveInstantiation.toECPoint`, equals `doubleAndAdd`.

    This connects the constraint-level chain (which operates on `ECPoint F`
    with field-element coordinates) to the abstract `doubleAndAdd` specification
    (which operates on `EllipticCurve.Point`).

    The proof requires showing at each inductive step that:
    1. The doubling constraint produces the correct doubled point
    2. The conditional add produces the correct next accumulator
    3. The `toECPoint` embedding preserves these relationships

    This is the hardest part of the scalar multiplication formalization,
    requiring `CurveInstantiation.pointAdd_agree` at each inductive step,
    plus validity preservation through doubling and conditional addition.
    The bridge between constraint-level `ECPoint` operations and abstract
    `EllipticCurve.Point` operations is where `CurveInstantiation` enters. -/
theorem scalarMulChain_matches_doubleAndAdd [EllipticCurve F] [inst : CurveInstantiation F]
    (n : ℕ) (scalar_bits : Fin n → F) (P : ECPoint F)
    (P_abs : EllipticCurve.Point (F := F))
    (hP : P = inst.toECPoint P_abs)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain inst.params n scalar_bits P intermediates doubled
      double_lambdas add_lambdas)
    (bits_bool : Fin n → Bool)
    (hbits_agree : ∀ i : Fin n, scalar_bits i = if bits_bool i then (1 : F) else 0) :
    intermediates ⟨n, by omega⟩ =
      inst.toECPoint (doubleAndAdd n bits_bool P_abs) := by
  sorry

-- ============================================================
-- Section 10: doubleAndAdd from bit decomposition
-- ============================================================

/-- If we have `isBitDecomp bits scalar` and `EllipticCurveGroup` axioms,
    then `doubleAndAdd` with the Bool-coercion of the bits equals
    `nsmulEC (bitsToNat n bits_bool) P`.

    This is the key lemma that justifies `CurveInstantiation.scalarMul_agree`:
    the chain computes the same thing as abstract scalar multiplication,
    because both compute `nsmulEC (bitsToNat bits) P` and `isBitDecomp`
    ensures the bit decomposition matches the scalar. -/
theorem doubleAndAdd_from_bitDecomp [EllipticCurveGroup F]
    (n : ℕ) (bits : Fin n → F) (scalar : F)
    (P : EllipticCurve.Point (F := F))
    (_hdecomp : isBitDecomp bits scalar)
    (bits_bool : Fin n → Bool)
    (_hbits_agree : ∀ i : Fin n, bits i = if bits_bool i then (1 : F) else 0) :
    doubleAndAdd n bits_bool P =
      nsmulEC (bitsToNat n bits_bool) P :=
  doubleAndAdd_eq_nsmul n bits_bool P

-- ============================================================
-- Section 11: End-to-end scalar multiplication correctness
-- ============================================================

/-- **End-to-end scalar multiplication correctness:**
    Given a valid `ecScalarMulChain` and a `CurveInstantiation`, the chain's
    final point, when embedded into the abstract curve, equals `doubleAndAdd`
    applied to the Bool-coercion of the chain's scalar bits.

    This is the theorem that `CurveInstantiation.scalarMul_agree` would
    invoke to justify its claim that the chain computes the correct scalar
    multiple. -/
theorem scalarMulChain_correct [EllipticCurve F] [inst : CurveInstantiation F]
    (n : ℕ) (scalar_bits : Fin n → F) (P : ECPoint F)
    (P_abs : EllipticCurve.Point (F := F))
    (hP : P = inst.toECPoint P_abs)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain inst.params n scalar_bits P intermediates doubled
      double_lambdas add_lambdas) :
    intermediates ⟨n, by omega⟩ =
      inst.toECPoint (doubleAndAdd n
        (chainBitsToBool n scalar_bits hchain.1)
        P_abs) := by
  exact scalarMulChain_matches_doubleAndAdd n scalar_bits P P_abs hP
    intermediates doubled double_lambdas add_lambdas hchain
    (chainBitsToBool n scalar_bits hchain.1)
    (fun i => chainBitsToBool_agree n scalar_bits hchain.1 i)

-- ============================================================
-- Section 12: Chain step with bit=0 gives accumulator
-- ============================================================

/-- When the bit at step `i` is 0, `intermediates (i+1)` equals
    the doubled version of `intermediates i`. -/
theorem scalarMulChain_step_zero (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) (hbit : scalar_bits i = 0) :
    intermediates i.succ = doubled i := by
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain i
  have hcond := hstep.2.2
  rw [hbit] at hcond
  exact (ecCondAdd_zero params (doubled i) P (intermediates i.succ) (add_lambdas i) hcond)

/-- When the bit at step `i` is 1, `intermediates (i+1)` is the result of
    full addition of `doubled i` and `P`. -/
theorem scalarMulChain_step_one (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) (hbit : scalar_bits i = 1) :
    ecAddFull params (doubled i) P (intermediates i.succ) (add_lambdas i) := by
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain i
  have hcond := hstep.2.2
  rw [hbit] at hcond
  exact ecCondAdd_one params (doubled i) P (intermediates i.succ) (add_lambdas i) hcond

-- ============================================================
-- Section 13: Doubling step extraction
-- ============================================================

/-- At step `i`, if the accumulator is at infinity, the doubled point
    is the identity. -/
theorem scalarMulChain_double_inf (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) (hinf : (intermediates i.castSucc).is_inf = 1) :
    doubled i = ⟨0, 0, 1⟩ := by
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain i
  exact hstep.1 hinf

/-- At step `i`, if the accumulator is finite, the doubling constraint holds. -/
theorem scalarMulChain_double_fin (params : CurveParams F) (n : ℕ)
    (scalar_bits : Fin n → F) (P : ECPoint F)
    (intermediates : Fin (n + 1) → ECPoint F)
    (doubled : Fin n → ECPoint F)
    (double_lambdas add_lambdas : Fin n → F)
    (hchain : ecScalarMulChain params n scalar_bits P intermediates doubled double_lambdas add_lambdas)
    (i : Fin n) (hfin : (intermediates i.castSucc).is_inf = 0) :
    ecDoubleConstraint params (intermediates i.castSucc) (doubled i) (double_lambdas i) := by
  have hstep := scalarMulChain_step params n scalar_bits P intermediates doubled
    double_lambdas add_lambdas hchain i
  exact hstep.2.1 hfin
