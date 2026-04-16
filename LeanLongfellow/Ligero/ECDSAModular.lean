import LeanLongfellow.Circuit.ECDSA.Spec
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

/-! # ECDSA Modular Arithmetic Decomposition

Decomposes the opaque `u1_bridge` / `u2_bridge` hypotheses from
`ECDSAWitnessValid` into transparent, verifiable sub-claims:
modular reductions with explicit quotients and range proofs,
modular inverse witnesses, and a key theorem connecting these
to the `ZMod` scalar computation used in `ecdsaVerify`. -/

-- ============================================================
-- Section 1: Modular Reduction and Inverse Structures
-- ============================================================

/-- Witness that `a mod n = rem` with explicit quotient and range proof. -/
structure ModularReduction (a n : ℕ) where
  quot : ℕ
  rem : ℕ
  eq : a = quot * n + rem
  range : rem < n

/-- Witness that `inv` is the modular inverse of `a` mod `n`. -/
structure ModularInverse (a n : ℕ) where
  inv : ℕ
  correct : (a * inv) % n = 1 % n
  range : inv < n

-- ============================================================
-- Section 2: ECDSA Scalar Computation
-- ============================================================

variable (F : Type*) [Field F]

/-- Full ECDSA scalar computation decomposed into verifiable steps.

    Given message hash `z` and signature `(r, s)`, the ECDSA scalars are:
    - `u1 = z * s⁻¹ mod groupOrder`
    - `u2 = r * s⁻¹ mod groupOrder`

    This structure witnesses each intermediate step with explicit
    quotients, remainders, and range proofs. -/
structure ECDSAScalarComputation [ec : EllipticCurveGroup F]
    (z : F) (sig : ECDSASignature F) where
  /-- Step 1: reduce `fieldToNat z` mod `groupOrder`. -/
  z_red : ModularReduction (ec.fieldToNat z) ec.groupOrder
  /-- Step 1: reduce `fieldToNat sig.s` mod `groupOrder`. -/
  s_red : ModularReduction (ec.fieldToNat sig.s) ec.groupOrder
  /-- Step 1: reduce `fieldToNat sig.r` mod `groupOrder`. -/
  r_red : ModularReduction (ec.fieldToNat sig.r) ec.groupOrder
  /-- Step 2: modular inverse of `s_red.rem` mod `groupOrder`. -/
  s_inv : ModularInverse s_red.rem ec.groupOrder
  /-- Step 3: reduce `z_red.rem * s_inv.inv` mod `groupOrder` to get `u1`. -/
  u1_product_red : ModularReduction (z_red.rem * s_inv.inv) ec.groupOrder
  /-- Step 4: reduce `r_red.rem * s_inv.inv` mod `groupOrder` to get `u2`. -/
  u2_product_red : ModularReduction (r_red.rem * s_inv.inv) ec.groupOrder

-- ============================================================
-- Section 3: Key Lemmas
-- ============================================================

/-- A modular reduction witness implies the cast to `ZMod n` agrees. -/
private theorem modRed_cast_eq {a n : ℕ} (red : ModularReduction a n) :
    (red.rem : ZMod n) = (a : ZMod n) := by
  have h := red.eq
  conv_rhs => rw [h]
  push_cast
  simp

/-- A modular reduction witness implies `rem = a % n`. -/
private theorem modRed_eq_mod {a n : ℕ} (red : ModularReduction a n) :
    red.rem = a % n := by
  have h := red.eq
  have := red.range
  simp only [h, Nat.mul_add_mod', Nat.mod_eq_of_lt this]

/-- A modular inverse witness implies the ZMod inverse relation,
    given that `n` is prime and `a ≠ 0 mod n`. -/
private theorem modInv_cast_eq {a n : ℕ} (hn : Nat.Prime n)
    (_ha : (a : ZMod n) ≠ 0)
    (mi : ModularInverse a n) :
    (mi.inv : ZMod n) = ((a : ZMod n))⁻¹ := by
  have hfact : Fact (Nat.Prime n) := ⟨hn⟩
  have hcorrect := mi.correct
  -- (a * inv) % n = 1 % n means (a * inv : ZMod n) = (1 : ZMod n)
  have hcast : (a : ZMod n) * (mi.inv : ZMod n) = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hcorrect, ZMod.natCast_mod, Nat.cast_one]
  exact (ZMod.inv_eq_of_mul_eq_one n _ _ hcast).symm

-- ============================================================
-- Section 4: Bridge Theorem
-- ============================================================

/-- **Key theorem**: an `ECDSAScalarComputation` implies the bridge
    equalities used in `ECDSAWitnessValid`.

    Specifically, the `u1` and `u2` remainders equal the `ZMod.val`
    of the abstract ECDSA scalar expressions. -/
theorem ecdsaScalarComputation_implies_bridge [ec : EllipticCurveGroup F]
    (z : F) (sig : ECDSASignature F)
    (comp : ECDSAScalarComputation F z sig)
    (hs_nonzero : (ec.fieldToNat sig.s : ZMod ec.groupOrder) ≠ 0) :
    comp.u1_product_red.rem =
      ZMod.val ((ec.fieldToNat z : ZMod ec.groupOrder) *
        ((ec.fieldToNat sig.s : ZMod ec.groupOrder))⁻¹) ∧
    comp.u2_product_red.rem =
      ZMod.val ((ec.fieldToNat sig.r : ZMod ec.groupOrder) *
        ((ec.fieldToNat sig.s : ZMod ec.groupOrder))⁻¹) := by
  have hprime := ec.hGroupOrder.out
  have hn_pos : ec.groupOrder ≠ 0 := Nat.Prime.ne_zero hprime
  have hfact : Fact (Nat.Prime ec.groupOrder) := ec.hGroupOrder
  -- Step 1: Cast equalities from reductions
  have hz_cast : (comp.z_red.rem : ZMod ec.groupOrder) =
      (ec.fieldToNat z : ZMod ec.groupOrder) :=
    modRed_cast_eq comp.z_red
  have hs_cast : (comp.s_red.rem : ZMod ec.groupOrder) =
      (ec.fieldToNat sig.s : ZMod ec.groupOrder) :=
    modRed_cast_eq comp.s_red
  have hr_cast : (comp.r_red.rem : ZMod ec.groupOrder) =
      (ec.fieldToNat sig.r : ZMod ec.groupOrder) :=
    modRed_cast_eq comp.r_red
  -- Step 2: s_red.rem ≠ 0 in ZMod (since fieldToNat sig.s ≠ 0 in ZMod)
  have hs_rem_ne : (comp.s_red.rem : ZMod ec.groupOrder) ≠ 0 := by
    rwa [hs_cast]
  -- Step 3: Inverse relation
  have hinv_cast : (comp.s_inv.inv : ZMod ec.groupOrder) =
      ((comp.s_red.rem : ZMod ec.groupOrder))⁻¹ :=
    modInv_cast_eq hprime hs_rem_ne comp.s_inv
  -- Step 4: Rewrite inverse in terms of original fieldToNat
  have hinv_orig : (comp.s_inv.inv : ZMod ec.groupOrder) =
      ((ec.fieldToNat sig.s : ZMod ec.groupOrder))⁻¹ := by
    rw [hinv_cast, hs_cast]
  -- Step 5: Product cast equalities
  have hu1_cast : (comp.u1_product_red.rem : ZMod ec.groupOrder) =
      (comp.z_red.rem : ZMod ec.groupOrder) * (comp.s_inv.inv : ZMod ec.groupOrder) := by
    have := modRed_cast_eq comp.u1_product_red
    push_cast at this ⊢; exact this
  have hu2_cast : (comp.u2_product_red.rem : ZMod ec.groupOrder) =
      (comp.r_red.rem : ZMod ec.groupOrder) * (comp.s_inv.inv : ZMod ec.groupOrder) := by
    have := modRed_cast_eq comp.u2_product_red
    push_cast at this ⊢; exact this
  -- Step 6: Combine to get the target expressions in ZMod
  have hu1_zmod : (comp.u1_product_red.rem : ZMod ec.groupOrder) =
      ((ec.fieldToNat z : ZMod ec.groupOrder) *
        ((ec.fieldToNat sig.s : ZMod ec.groupOrder))⁻¹) := by
    rw [hu1_cast, hz_cast, hinv_orig]
  have hu2_zmod : (comp.u2_product_red.rem : ZMod ec.groupOrder) =
      ((ec.fieldToNat sig.r : ZMod ec.groupOrder) *
        ((ec.fieldToNat sig.s : ZMod ec.groupOrder))⁻¹) := by
    rw [hu2_cast, hr_cast, hinv_orig]
  -- Step 7: Extract via ZMod.val
  constructor
  · have hrange := comp.u1_product_red.range
    rw [← ZMod.val_natCast_of_lt hrange, hu1_zmod]
  · have hrange := comp.u2_product_red.range
    rw [← ZMod.val_natCast_of_lt hrange, hu2_zmod]
