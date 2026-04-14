import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.Basic

open Finset

variable {F : Type*} [Field F]

/-- A system of linear constraints: A · w = b. -/
structure LinearConstraints (F : Type*) [Field F] (m n : ℕ) where
  matrix : Fin m → Fin n → F
  target : Fin m → F

/-- A single quadratic constraint: w[left] · w[right] = w[output]. -/
structure QuadConstraint (n : ℕ) where
  left : Fin n
  right : Fin n
  output : Fin n

/-- A witness satisfies the linear constraints. -/
def satisfiesLinear {m n : ℕ} (w : Fin n → F) (lc : LinearConstraints F m n) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, lc.matrix i j * w j = lc.target i

/-- A witness satisfies a quadratic constraint. -/
def satisfiesQuad {n : ℕ} (w : Fin n → F) (qc : QuadConstraint n) : Prop :=
  w qc.left * w qc.right = w qc.output

/-- A witness satisfies all constraints. -/
def satisfiesAll {m n q : ℕ} (w : Fin n → F)
    (lcs : LinearConstraints F m n) (qcs : Fin q → QuadConstraint n) : Prop :=
  satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i)

theorem satisfiesAll_iff {m n q : ℕ} (w : Fin n → F)
    (lcs : LinearConstraints F m n) (qcs : Fin q → QuadConstraint n) :
    satisfiesAll w lcs qcs ↔ satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i) :=
  Iff.rfl
