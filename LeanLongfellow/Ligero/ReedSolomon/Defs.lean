import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

variable {F : Type*} [Field F]

/-- An evaluation domain: `N` distinct points in a field `F`. -/
structure EvalDomain (F : Type*) [Field F] (N : ℕ) where
  points : Fin N → F
  distinct : Function.Injective points

/-- Encode a polynomial given by its coefficients into a codeword
    by evaluating at every domain point. -/
noncomputable def rsEncode {F : Type*} [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (coeffs : Fin k → F) : Fin N → F :=
  fun i => (∑ j : Fin k, Polynomial.C (coeffs j) * Polynomial.X ^ (j : ℕ)).eval (domain.points i)

/-- A word is a valid Reed-Solomon codeword iff it is the encoding
    of some coefficient vector. -/
def isRSCodeword {F : Type*} [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (word : Fin N → F) : Prop :=
  ∃ coeffs : Fin k → F, word = rsEncode domain k coeffs

/-- The Reed-Solomon code: the set of all valid codewords. -/
def rsCode (F : Type*) [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) : Set (Fin N → F) :=
  { w | isRSCodeword domain k w }

/-! ### Helper lemmas -/

/-- The polynomial constructed from coefficients. -/
noncomputable def coeffsToPoly {k : ℕ} (coeffs : Fin k → F) : Polynomial F :=
  ∑ j : Fin k, Polynomial.C (coeffs j) * Polynomial.X ^ (j : ℕ)

/-- `rsEncode` is evaluation of `coeffsToPoly` at the domain points. -/
theorem rsEncode_eq_poly_eval {N : ℕ} (domain : EvalDomain F N)
    (k : ℕ) (coeffs : Fin k → F) (i : Fin N) :
    rsEncode domain k coeffs i = (coeffsToPoly coeffs).eval (domain.points i) := by
  rfl
