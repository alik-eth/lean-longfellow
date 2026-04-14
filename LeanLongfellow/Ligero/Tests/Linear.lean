import LeanLongfellow.Ligero.Constraints
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.Defs

open Finset

/-! # Ligero Linear Constraint Test

The linear test checks that a committed witness `w` satisfies `A · w = b`.
The verifier combines `m` constraints with random field elements `α[0..m-1]`
into a single constraint and checks the combined inner product against the
combined target.

## Main results

- `linearTestAccepts`: the verifier's acceptance predicate after combining
  constraints with random `α`.
- `linearTest_actual_dot`: the sum-swap identity showing the combined inner
  product equals the α-weighted sum of individual inner products.
- `linearTest_soundness_det`: if the witness violates some constraint, then
  there exists a violated row.
- `linearTest_soundness`: if the witness violates some constraint and the
  prover provides the honest dot product, the verifier rejects whenever
  the α-weighted error is nonzero.
-/

variable {F : Type*} [Field F]

/-- The linear constraint test: after combining m constraints with random α,
    check that the prover's claimed dot product equals the combined target
    ∑_c α[c] · b[c]. -/
def linearTestAccepts {m n : ℕ}
    (_w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F)
    (dot_claim : F) : Prop :=
  dot_claim = ∑ c : Fin m, alpha c * lcs.target c

/-- The actual combined inner product: ∑_j (∑_c α[c] · A[c][j]) · w[j].
    This is what the honest prover would provide as dot_claim. -/
def actualDot {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F) : F :=
  ∑ j : Fin n, (∑ c : Fin m, alpha c * lcs.matrix c j) * w j

/-- The combined target: ∑_c α[c] · b[c]. -/
def combinedTarget {m n : ℕ}
    (lcs : LinearConstraints F m n) (alpha : Fin m → F) : F :=
  ∑ c : Fin m, alpha c * lcs.target c

/-- Sum-swap identity: the combined inner product equals the α-weighted sum
    of individual row-inner-products.

    ∑_j (∑_c α[c] · A[c][j]) · w[j] = ∑_c α[c] · (∑_j A[c][j] · w[j])

    This is the key algebraic identity underlying the linear test. -/
theorem linearTest_actual_dot {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F) :
    ∑ j : Fin n, (∑ c : Fin m, alpha c * lcs.matrix c j) * w j =
      ∑ c : Fin m, alpha c * (∑ j : Fin n, lcs.matrix c j * w j) := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- If the witness satisfies all linear constraints, then the actual combined
    inner product equals the combined target. This is completeness: an honest
    prover always passes the test. -/
theorem linearTest_completeness {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F)
    (h_sat : satisfiesLinear w lcs) :
    actualDot w lcs alpha = combinedTarget lcs alpha := by
  unfold actualDot combinedTarget
  rw [linearTest_actual_dot]
  congr 1
  ext c
  rw [h_sat c]

/-- If the witness does NOT satisfy the linear constraints, then there exists
    a violated constraint row c₀ with ∑_j A[c₀][j] · w[j] ≠ b[c₀].

    This is the deterministic extraction of a violated row from the negation
    of satisfiesLinear. -/
theorem linearTest_soundness_det {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h_viol : ¬ satisfiesLinear w lcs) :
    ∃ c₀ : Fin m,
      ∑ j : Fin n, lcs.matrix c₀ j * w j ≠ lcs.target c₀ := by
  unfold satisfiesLinear at h_viol
  by_contra h_all
  apply h_viol
  intro i
  by_contra h_ne
  exact h_all ⟨i, h_ne⟩

/-- The error for constraint row c: (∑_j A[c][j] · w[j]) - b[c]. -/
def rowError {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (c : Fin m) : F :=
  (∑ j : Fin n, lcs.matrix c j * w j) - lcs.target c

/-- The actual combined inner product minus the combined target equals the
    α-weighted sum of row errors. -/
theorem linearTest_error_eq {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F) :
    actualDot w lcs alpha - combinedTarget lcs alpha =
      ∑ c : Fin m, alpha c * rowError w lcs c := by
  unfold actualDot combinedTarget rowError
  rw [linearTest_actual_dot]
  -- Goal: ∑ c, α[c] * (∑ j, A[c][j]*w[j]) - ∑ c, α[c] * target[c]
  --     = ∑ c, α[c] * ((∑ j, A[c][j]*w[j]) - target[c])
  -- Factor the subtraction into the sum
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext c
  rw [mul_sub]

/-- Soundness: if the witness violates some constraint and the prover provides
    the honest dot product, the test rejects whenever the α-weighted error
    ∑_c α[c] · error[c] is nonzero. -/
theorem linearTest_soundness {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F)
    (h_err : ∑ c : Fin m, alpha c * rowError w lcs c ≠ 0) :
    ¬ linearTestAccepts w lcs alpha (actualDot w lcs alpha) := by
  intro h_acc
  apply h_err
  unfold linearTestAccepts at h_acc
  -- h_acc: actualDot = combinedTarget
  have h_eq := linearTest_error_eq w lcs alpha
  unfold combinedTarget at h_eq
  rw [h_acc, sub_self] at h_eq
  exact h_eq.symm

/-- Converse: if the α-weighted error is zero, the honest prover passes. -/
theorem linearTest_accept_iff_zero_error {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F) :
    linearTestAccepts w lcs alpha (actualDot w lcs alpha) ↔
      ∑ c : Fin m, alpha c * rowError w lcs c = 0 := by
  constructor
  · intro h_acc
    unfold linearTestAccepts at h_acc
    have h_eq := linearTest_error_eq w lcs alpha
    unfold combinedTarget at h_eq
    rw [h_acc, sub_self] at h_eq
    exact h_eq.symm
  · intro h_zero
    unfold linearTestAccepts
    have h_eq := linearTest_error_eq w lcs alpha
    unfold combinedTarget at h_eq
    rw [h_zero] at h_eq
    exact sub_eq_zero.mp h_eq
