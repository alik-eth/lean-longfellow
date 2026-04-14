import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

open Finset

/-! # Predicate Gadgets for Arithmetic Circuit Verification

Reusable circuit fragments that enforce predicates on witness values.
Each gadget is a Prop about field elements, paired with a correctness theorem.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Boolean Constraint
-- ============================================================

/-- A field element is boolean: x ∈ {0, 1}. -/
def isBool (x : F) : Prop := x * (1 - x) = 0

theorem isBool_iff (x : F) : isBool x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    have hmz := mul_eq_zero.mp h
    rcases hmz with hx | hx
    · left; exact hx
    · right; exact (sub_eq_zero.mp hx).symm
  · rintro (rfl | rfl) <;> unfold isBool <;> ring

-- ============================================================
-- Section 2: Bit Decomposition
-- ============================================================

/-- A vector of field elements represents the bits of v:
    v = ∑ᵢ bits(i) * 2^i, and each bit is boolean. -/
def isBitDecomp {n : ℕ} (bits : Fin n → F) (v : F) : Prop :=
  (∀ i, isBool (bits i)) ∧
  v = ∑ i : Fin n, bits i * (2 : F) ^ (i : ℕ)

/-- If bits are a valid decomposition, each bit is 0 or 1. -/
theorem isBitDecomp_bits_bool {n : ℕ} (bits : Fin n → F) (v : F)
    (h : isBitDecomp bits v) (i : Fin n) : bits i = 0 ∨ bits i = 1 :=
  (isBool_iff _).mp (h.1 i)

-- ============================================================
-- Section 3: Range Check
-- ============================================================

/-- A field element is in range [0, 2^n - 1]:
    there exist n bits that decompose to v. -/
def inRange (n : ℕ) (v : F) : Prop :=
  ∃ bits : Fin n → F, isBitDecomp bits v

/-- If v has an n-bit decomposition, v equals a sum of powers of 2. -/
theorem inRange_sum {n : ℕ} (bits : Fin n → F) (v : F)
    (h : isBitDecomp bits v) :
    v = ∑ i : Fin n, bits i * (2 : F) ^ (i : ℕ) := h.2

-- ============================================================
-- Section 4: Equality Check
-- ============================================================

/-- Two field elements are equal (as a constraint). -/
def eqCheck (a b : F) : Prop := a - b = 0

theorem eqCheck_iff (a b : F) : eqCheck a b ↔ a = b := by
  unfold eqCheck
  exact sub_eq_zero

-- ============================================================
-- Section 5: Nonzero / Inverse Witness
-- ============================================================

/-- A field element is nonzero, witnessed by its inverse. -/
def isNonzero (a a_inv : F) : Prop := a * a_inv = 1

theorem isNonzero_ne_zero (a a_inv : F) (h : isNonzero a a_inv) : a ≠ 0 := by
  intro ha
  unfold isNonzero at h
  rw [ha, zero_mul] at h
  exact zero_ne_one h

-- ============================================================
-- Section 6: Conditional Select
-- ============================================================

/-- Conditional select: if b is boolean, result = b*x + (1-b)*y.
    When b=1, result=x. When b=0, result=y. -/
def condSelect (b x y result : F) : Prop :=
  isBool b ∧ result = b * x + (1 - b) * y

theorem condSelect_true (x y : F) : condSelect (1 : F) x y x :=
  ⟨(isBool_iff _).mpr (Or.inr rfl), by ring⟩

theorem condSelect_false (x y : F) : condSelect (0 : F) x y y :=
  ⟨(isBool_iff _).mpr (Or.inl rfl), by ring⟩

-- ============================================================
-- Section 7: XOR Gate
-- ============================================================

/-- XOR as field arithmetic: a ⊕ b = a + b - 2ab. -/
def boolXor (a b result : F) : Prop :=
  isBool a ∧ isBool b ∧ isBool result ∧ result = a + b - 2 * a * b

private theorem isBool_zero : isBool (0 : F) := (isBool_iff _).mpr (Or.inl rfl)
private theorem isBool_one : isBool (1 : F) := (isBool_iff _).mpr (Or.inr rfl)

theorem boolXor_correct_00 : boolXor (0 : F) (0 : F) (0 : F) :=
  ⟨isBool_zero, isBool_zero, isBool_zero, by ring⟩

theorem boolXor_correct_01 : boolXor (0 : F) (1 : F) (1 : F) :=
  ⟨isBool_zero, isBool_one, isBool_one, by ring⟩

theorem boolXor_correct_10 : boolXor (1 : F) (0 : F) (1 : F) :=
  ⟨isBool_one, isBool_zero, isBool_one, by ring⟩

theorem boolXor_correct_11 : boolXor (1 : F) (1 : F) (0 : F) :=
  ⟨isBool_one, isBool_one, isBool_zero, by ring⟩

-- ============================================================
-- Section 8: AND Gate
-- ============================================================

/-- AND as field arithmetic: a ∧ b = a * b. -/
def boolAnd (a b result : F) : Prop :=
  isBool a ∧ isBool b ∧ result = a * b

theorem boolAnd_correct_00 : boolAnd (0 : F) (0 : F) (0 : F) :=
  ⟨isBool_zero, isBool_zero, by ring⟩

theorem boolAnd_correct_01 : boolAnd (0 : F) (1 : F) (0 : F) :=
  ⟨isBool_zero, isBool_one, by ring⟩

theorem boolAnd_correct_10 : boolAnd (1 : F) (0 : F) (0 : F) :=
  ⟨isBool_one, isBool_zero, by ring⟩

theorem boolAnd_correct_11 : boolAnd (1 : F) (1 : F) (1 : F) :=
  ⟨isBool_one, isBool_one, by ring⟩
