import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.CharP.Basic
import LeanLongfellow.Ligero.ReedSolomon.Defs

/-!
# Concrete Evaluation Domain Constructions

This file provides two concrete constructions of `EvalDomain` together with
proofs that their point-sequences are injective (i.e., the points are distinct):

1. **Roots-of-unity domain**: `{1, ω, ω², ..., ω^(N-1)}` where `ω` is a
   primitive `N`-th root of unity.

2. **Arithmetic-progression domain**: `{a, a+d, a+2d, ..., a+(N-1)d}` where
   the step `d` is nonzero and the field characteristic does not divide
   any positive index difference (ensured by a `CharP` hypothesis).
-/

variable {F : Type*} [Field F]

/-! ### 1. Roots-of-unity domain -/

/-- Powers `ω^0, ω^1, …, ω^(N-1)` of a primitive `N`-th root of unity are
    pairwise distinct, so they form a valid evaluation domain. -/
def rootsOfUnityDomain (N : ℕ) (omega : F)
    (hprim : IsPrimitiveRoot omega N) : EvalDomain F N where
  points := fun i => omega ^ i.val
  distinct := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ h
    simp only at h
    have heq : i = j := hprim.pow_inj hi hj h
    exact Fin.ext heq

/-! ### 2. Arithmetic-progression domain -/

/-- `a + d * i` as a function of `i : Fin N` is injective when `d ≠ 0` and
    the natural-number cast `ℕ → F` is injective on `{0, …, N-1}`.

    The cast-injectivity hypothesis `hcast` is satisfied whenever the
    characteristic `p` of `F` is either `0` or `≥ N`. -/
def arithmeticDomain (N : ℕ) (a d : F) (hd : d ≠ 0)
    (hcast : Function.Injective (fun n : Fin N => (n.val : F))) :
    EvalDomain F N where
  points := fun i => a + d * (i.val : F)
  distinct := by
    intro i j h
    simp only at h
    -- `a + d * ↑i = a + d * ↑j` ⟹ `d * ↑i = d * ↑j` ⟹ `↑i = ↑j`
    have hcancel : d * (i.val : F) = d * (j.val : F) := add_left_cancel h
    have hzero : (i.val : F) = (j.val : F) := mul_left_cancel₀ hd hcancel
    exact hcast (by exact_mod_cast hzero)

/-! ### Helpers for the cast-injectivity hypothesis -/

/-- When the characteristic is `0`, `ℕ → F` is injective on `Fin N`. -/
lemma fin_natCast_injective_of_charZero [CharZero F] (N : ℕ) :
    Function.Injective (fun n : Fin N => (n.val : F)) := by
  intro ⟨i, _⟩ ⟨j, _⟩ h
  simp only at h
  have : i = j := Nat.cast_injective h
  exact Fin.ext this

/-- When the characteristic `p ≥ N` (including `p = 0`), `ℕ → F` is injective
    on `Fin N`. -/
lemma fin_natCast_injective_of_char_ge (N p : ℕ) [CharP F p] (hp : N ≤ p ∨ p = 0) :
    Function.Injective (fun n : Fin N => (n.val : F)) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only at h
  suffices i = j from Fin.ext this
  rcases hp with hp | rfl
  · -- char p ≥ N, so cast is injective on {0, …, N-1} ⊆ {0, …, p-1}
    have hi' : i < p := lt_of_lt_of_le hi hp
    have hj' : j < p := lt_of_lt_of_le hj hp
    exact CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr hi') (Set.mem_Iio.mpr hj') h
  · -- char 0: CharP F 0 is CharZero
    haveI : CharZero F := CharP.charP_to_charZero F
    exact Nat.cast_injective h

/-! ### Convenience constructors -/

/-- Roots-of-unity evaluation domain (main constructor). -/
def evalDomainRootsOfUnity (N : ℕ) (omega : F) (hprim : IsPrimitiveRoot omega N) :
    EvalDomain F N :=
  rootsOfUnityDomain N omega hprim

/-- Arithmetic-progression evaluation domain when `char F = 0` or `char F ≥ N`. -/
def evalDomainArithmetic (N : ℕ) (a d : F) (hd : d ≠ 0)
    (p : ℕ) [CharP F p] (hp : N ≤ p ∨ p = 0) : EvalDomain F N :=
  arithmeticDomain N a d hd (fin_natCast_injective_of_char_ge N p hp)
