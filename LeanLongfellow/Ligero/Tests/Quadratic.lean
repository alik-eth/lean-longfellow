import LeanLongfellow.Ligero.Constraints
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs

open Finset

/-! # Ligero Quadratic Constraint Test

Quadratic constraints are of the form `w[left] * w[right] = w[output]`.
The verifier combines `q` constraints with random field elements `u[0..q-1]`
and checks that the combined error
  `∑ u[i] * (w[qcs[i].left] * w[qcs[i].right] - w[qcs[i].output])`
is zero.

## Main results

- `quadraticTestAccepts`: the algebraic acceptance predicate — all quadratic
  constraints are satisfied.
- `quadraticTest_sound`: if the test accepts, every constraint is satisfied.
- `combinedQuadError`: the random linear combination of individual constraint
  errors.
- `combinedQuadError_zero_of_sat`: completeness — if all constraints are
  satisfied, the combined error is zero for any `u`.
- `quadTest_violated_exists`: if some constraint is violated, extract a
  witness for the violated index.
-/

variable {F : Type*} [Field F]

/-- The quadratic constraint test: given a witness, check that all
    quadratic constraints are satisfied. This is the algebraic core
    — the tableau/codeword structure is handled separately. -/
def quadraticTestAccepts {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) : Prop :=
  ∀ i : Fin q, satisfiesQuad w (qcs i)

/-- If the quadratic test accepts, all quadratic constraints are satisfied. -/
theorem quadraticTest_sound {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h : quadraticTestAccepts w qcs) :
    ∀ i, satisfiesQuad w (qcs i) := h

/-- The error for a single quadratic constraint:
    `w[left] * w[right] - w[output]`. -/
def quadError {n : ℕ}
    (w : Fin n → F) (qc : QuadConstraint n) : F :=
  w qc.left * w qc.right - w qc.output

/-- The constraint is satisfied iff its error is zero. -/
theorem satisfiesQuad_iff_error_zero {n : ℕ}
    (w : Fin n → F) (qc : QuadConstraint n) :
    satisfiesQuad w qc ↔ quadError w qc = 0 := by
  unfold satisfiesQuad quadError
  exact sub_eq_zero.symm

/-- The combined quadratic check: the verifier samples `u[0..q-1]` and checks
    `∑ u[i] * (w[qcs[i].left] * w[qcs[i].right] - w[qcs[i].output]) = 0`.
    If some constraint is violated, this is a nonzero degree-1 polynomial
    in the `u` variables, so Schwartz-Zippel applies. -/
def combinedQuadError {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) (u : Fin q → F) : F :=
  ∑ i : Fin q, u i * (w (qcs i).left * w (qcs i).right - w (qcs i).output)

/-- `combinedQuadError` equals the `u`-weighted sum of individual errors. -/
theorem combinedQuadError_eq_sum {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) (u : Fin q → F) :
    combinedQuadError w qcs u = ∑ i : Fin q, u i * quadError w (qcs i) := by
  unfold combinedQuadError quadError
  rfl

/-- If all constraints are satisfied, the combined error is zero for any `u`. -/
theorem combinedQuadError_zero_of_sat {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_sat : ∀ i, satisfiesQuad w (qcs i)) (u : Fin q → F) :
    combinedQuadError w qcs u = 0 := by
  unfold combinedQuadError satisfiesQuad at *
  apply Finset.sum_eq_zero
  intro i _
  rw [h_sat i, sub_self, mul_zero]

/-- If some constraint is violated, there exists `i₀` such that
    `w[left] * w[right] ≠ w[output]`. -/
theorem quadTest_violated_exists {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ ∀ i, satisfiesQuad w (qcs i)) :
    ∃ i₀ : Fin q, w (qcs i₀).left * w (qcs i₀).right ≠ w (qcs i₀).output := by
  by_contra h_all
  apply h_viol
  intro i
  by_contra h_ne
  exact h_all ⟨i, h_ne⟩

/-- Completeness: if the witness satisfies all quadratic constraints, the
    quadratic test accepts. -/
theorem quadraticTest_completeness {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_sat : ∀ i, satisfiesQuad w (qcs i)) :
    quadraticTestAccepts w qcs :=
  h_sat

/-- If the combined error is nonzero, at least one constraint is violated. -/
theorem quadTest_unsound_of_nonzero_error {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) (u : Fin q → F)
    (h_err : combinedQuadError w qcs u ≠ 0) :
    ¬ quadraticTestAccepts w qcs := by
  intro h_acc
  exact h_err (combinedQuadError_zero_of_sat w qcs h_acc u)
