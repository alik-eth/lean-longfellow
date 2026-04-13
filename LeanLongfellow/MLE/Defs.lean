import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open Finset

/-- A multilinear polynomial over `n` variables with coefficients in `F`.
    Represented as its evaluation table over `{0,1}^n`. -/
structure MultilinearPoly (F : Type*) [Field F] (n : ℕ) where
  table : (Fin n → Bool) → F

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Cast a Boolean assignment to field elements: `true ↦ 1`, `false ↦ 0`. -/
def boolToField (b : Fin n → Bool) : Fin n → F :=
  fun i => if b i then 1 else 0

/-- Lagrange basis polynomial for Boolean vector `b`, evaluated at point `x`.
    `lagrangeBasis b x = ∏ᵢ (bᵢ · xᵢ + (1 - bᵢ) · (1 - xᵢ))` -/
def lagrangeBasis (b : Fin n → Bool) (x : Fin n → F) : F :=
  ∏ i : Fin n, if b i then x i else 1 - x i

end MultilinearPoly
