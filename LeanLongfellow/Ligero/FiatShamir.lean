import LeanLongfellow.Ligero.Concrete
import LeanLongfellow.Ligero.Tests.Linear
import LeanLongfellow.Ligero.Tests.Quadratic
import LeanLongfellow.FiatShamir.Oracle

/-! # Non-Interactive Ligero via Fiat-Shamir

Compiles the interactive three-test Ligero protocol into a non-interactive
one by deriving verifier challenges from a random oracle.

The soundness bound: for a non-adaptive adversary, the probability of
fooling the non-interactive verifier is bounded by the sum of the
per-test error probabilities.

## Main definitions

- `linearTestSingleChallenge`: probabilistic linear test with a single random
  challenge vector alpha.
- `quadTestSingleChallenge`: probabilistic quadratic test with a single random
  challenge vector u.

## Main results

- `linearTest_prob_soundness`: if the witness violates some linear constraint,
  the single-challenge test passes on at most `|F|^(m-1)` challenge vectors.
- `quadTest_prob_soundness`: if some quadratic constraint is violated, the
  single-challenge test passes on at most `|F|^(q-1)` challenge vectors.

The bound `|F|^(k-1)` out of `|F|^k` total challenge vectors gives
probability `1/|F|` per test.
-/

open Finset Polynomial Classical

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Single-challenge test definitions
-- ============================================================

/-- Single-challenge linear test (probabilistic):
    Instead of checking for ALL alpha, check for ONE random alpha.
    The verifier draws `alpha : Fin m -> F` uniformly at random and checks
    `actualDot w lcs alpha = combinedTarget lcs alpha`. -/
def linearTestSingleChallenge {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (alpha : Fin m → F) : Prop :=
  actualDot w lcs alpha = combinedTarget lcs alpha

/-- Single-challenge quadratic test (probabilistic):
    Instead of checking for ALL u, check for ONE random u.
    The verifier draws `u : Fin q -> F` uniformly at random and checks
    `combinedQuadError w qcs u = 0`. -/
def quadTestSingleChallenge {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (u : Fin q → F) : Prop :=
  combinedQuadError w qcs u = 0

-- ============================================================
-- Section 2: Single-challenge completeness
-- ============================================================

/-- Completeness of the single-challenge linear test: if the witness
    satisfies all linear constraints, the test always passes. -/
theorem linearTestSingle_completeness {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F)
    (h_sat : satisfiesLinear w lcs) :
    linearTestSingleChallenge w lcs alpha :=
  linearTest_completeness w lcs alpha h_sat

/-- Completeness of the single-challenge quadratic test: if all quadratic
    constraints are satisfied, the test always passes. -/
theorem quadTestSingle_completeness {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) (u : Fin q → F)
    (h_sat : ∀ i, satisfiesQuad w (qcs i)) :
    quadTestSingleChallenge w qcs u :=
  combinedQuadError_zero_of_sat w qcs h_sat u

-- ============================================================
-- Section 3: Probabilistic soundness — linear test
-- ============================================================

/-- The linear test acceptance condition is equivalent to the weighted
    row error being zero. -/
private theorem linearTestSingle_iff_error_zero {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n) (alpha : Fin m → F) :
    linearTestSingleChallenge w lcs alpha ↔
      ∑ c : Fin m, alpha c * rowError w lcs c = 0 := by
  unfold linearTestSingleChallenge
  constructor
  · intro h
    have := linearTest_error_eq w lcs alpha
    rw [h, sub_self] at this
    exact this.symm
  · intro h
    have := linearTest_error_eq w lcs alpha
    rw [h] at this
    exact sub_eq_zero.mp this

/-- Helper: the degree of `C a * X + C b` is at most 1. -/
private theorem natDegree_linear_poly_le (a b : F) :
    (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree ≤ 1 := by
  calc (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      ≤ max (Polynomial.C a * Polynomial.X).natDegree
            (Polynomial.C b).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ 1 := by
        apply Nat.max_le.mpr
        constructor
        · calc (Polynomial.C a * Polynomial.X).natDegree
              ≤ (Polynomial.C a).natDegree + Polynomial.X.natDegree :=
                Polynomial.natDegree_mul_le
            _ ≤ 0 + 1 := by
                apply Nat.add_le_add
                · exact (Polynomial.natDegree_C a).le
                · exact le_of_eq Polynomial.natDegree_X
            _ = 1 := by omega
        · exact le_trans (Polynomial.natDegree_C b).le (Nat.zero_le _)

/-- The quadratic test acceptance condition is equivalent to the weighted
    quad error being zero. -/
private theorem quadTestSingle_iff_error_zero {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n) (u : Fin q → F) :
    quadTestSingleChallenge w qcs u ↔
      ∑ i : Fin q, u i * quadError w (qcs i) = 0 := by
  unfold quadTestSingleChallenge
  rw [combinedQuadError_eq_sum]

-- ============================================================
-- Section 5: Non-interactive Ligero verification
-- ============================================================

/-- Non-interactive Ligero proof: the proof data plus the challenges
    derived from a random oracle.
    The random oracle provides:
    - `m` field elements for the linear test (alpha challenges)
    - `q` field elements for the quadratic test (u challenges) -/
structure NILigeroProof (F : Type*) [Field F] (params : LigeroParams) (m n q : ℕ) where
  /-- The interactive proof data -/
  proof : LigeroProof F params m n q
  /-- Random oracle output for linear test -/
  alpha : Fin m → F
  /-- Random oracle output for quadratic test -/
  u : Fin q → F

/-- Non-interactive Ligero verification: the verifier checks the LDT
    (with the prover's LDT challenge), plus the single-challenge
    linear and quadratic tests using oracle-derived challenges.

    This is a probabilistic verify: the verifier is parameterized by
    the random oracle output (alpha, u). -/
def niLigeroVerify {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q) : Prop :=
  combinedRowIsCodeword niProof.proof.domain niProof.proof.tableau niProof.proof.ldt_u ∧
  linearTestSingleChallenge w lcs niProof.alpha ∧
  quadTestSingleChallenge w qcs niProof.u

/-- **Non-interactive Ligero completeness**: if the witness satisfies all
    constraints and the LDT passes, the non-interactive verifier accepts
    for any oracle output. -/
theorem niLigero_completeness {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (h_ldt : combinedRowIsCodeword niProof.proof.domain niProof.proof.tableau
               niProof.proof.ldt_u)
    (h_sat : satisfiesAll w lcs qcs) :
    niLigeroVerify w lcs qcs niProof :=
  ⟨h_ldt,
   linearTestSingle_completeness w lcs niProof.alpha h_sat.1,
   quadTestSingle_completeness w qcs niProof.u h_sat.2⟩

-- ============================================================
-- Soundness proofs require DecidableEq and Fintype for countSat
-- ============================================================

variable [DecidableEq F] [Fintype F]

/-- **Probabilistic linear test soundness**: if the witness violates some
    linear constraint, the single-challenge test passes on at most
    `|F|^(m-1)` challenge vectors out of `|F|^m` total.

    This gives a soundness error of `1/|F|`.

    Proof idea: from `h_viol`, extract a violated row `c_0` with
    `rowError w lcs c_0 != 0`. The acceptance condition
    `sum_c alpha[c] * rowError[c] = 0` is a degree-1 polynomial in
    `alpha[c_0]` with nonzero leading coefficient. For each fixing of
    the other `m-1` coordinates, at most one value of `alpha[c_0]`
    makes this zero. So the count is at most `|F|^(m-1)`. -/
noncomputable def linearTest_prob_soundness {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h_viol : ¬ satisfiesLinear w lcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
      Fintype.card F ^ (m - 1) := by
  -- Extract a violated row c₀
  obtain ⟨c₀, hc₀⟩ := linearTest_soundness_det w lcs h_viol
  -- The error for row c₀ is nonzero
  have h_err_ne : rowError w lcs c₀ ≠ 0 := by
    intro h; apply hc₀; unfold rowError at h; exact sub_eq_zero.mp h
  -- Rewrite the acceptance condition in terms of the error
  have h_rewrite : ∀ alpha, linearTestSingleChallenge w lcs alpha ↔
      ∑ c : Fin m, alpha c * rowError w lcs c = 0 :=
    fun alpha => linearTestSingle_iff_error_zero w lcs alpha
  -- Reduce to counting error = 0
  suffices h : countSat (fun alpha : Fin m → F =>
      ∑ c : Fin m, alpha c * rowError w lcs c = 0) ≤
        Fintype.card F ^ (m - 1) by
    calc countSat (fun alpha => linearTestSingleChallenge w lcs alpha)
        ≤ countSat (fun alpha => ∑ c : Fin m, alpha c * rowError w lcs c = 0) := by
          unfold countSat
          apply Finset.card_le_card
          intro alpha h_mem
          rw [Finset.mem_filter] at h_mem ⊢
          exact ⟨h_mem.1, (h_rewrite alpha).mp h_mem.2⟩
      _ ≤ Fintype.card F ^ (m - 1) := h
  -- Model the error as a degree-1 polynomial in alpha[c₀]:
  -- D(alpha) = C(rowError c₀) * X + C(∑_{c ≠ c₀} alpha[c] * rowError[c])
  let D : (Fin m → F) → Polynomial F := fun alpha =>
    Polynomial.C (rowError w lcs c₀) * Polynomial.X +
    Polynomial.C (∑ c ∈ Finset.univ.erase c₀, alpha c * rowError w lcs c)
  -- D alpha evaluates at alpha[c₀] to the weighted error sum
  have h_eval : ∀ alpha, (D alpha).eval (alpha c₀) =
      ∑ c : Fin m, alpha c * rowError w lcs c := by
    intro alpha
    simp only [D, eval_add, eval_mul, eval_C, eval_X]
    rw [← Finset.add_sum_erase Finset.univ (fun c => alpha c * rowError w lcs c)
          (Finset.mem_univ c₀)]
    ring
  -- D alpha is always nonzero (coefficient of X is rowError c₀ ≠ 0)
  have h_D_ne : ∀ alpha, D alpha ≠ 0 := by
    intro alpha h_eq
    have : (D alpha).coeff 1 = 0 := by rw [h_eq]; simp
    simp only [D, coeff_add, coeff_C_mul, coeff_X, mul_one, coeff_C, Nat.one_ne_zero,
               ↓reduceIte, add_zero] at this
    exact h_err_ne this
  -- Equivalence: error = 0 iff D vanishes at alpha[c₀]
  have h_equiv : ∀ alpha, (∑ c : Fin m, alpha c * rowError w lcs c = 0) ↔
      (D alpha ≠ 0 ∧ (D alpha).eval (alpha c₀) = 0) := by
    intro alpha
    exact ⟨fun h_sum => ⟨h_D_ne alpha, by rw [h_eval]; exact h_sum⟩,
           fun ⟨_, h_root⟩ => by rw [h_eval] at h_root; exact h_root⟩
  calc countSat (fun alpha => ∑ c : Fin m, alpha c * rowError w lcs c = 0)
      ≤ countSat (fun alpha => D alpha ≠ 0 ∧ (D alpha).eval (alpha c₀) = 0) := by
        unfold countSat
        apply Finset.card_le_card
        intro alpha h_mem
        rw [Finset.mem_filter] at h_mem ⊢
        exact ⟨h_mem.1, (h_equiv alpha).mp h_mem.2⟩
    _ ≤ 1 * Fintype.card F ^ (m - 1) := by
        apply countSat_adaptive_root c₀ D
        · -- Independence: D depends only on alpha[c] for c ≠ c₀
          intro cs cs' hagree
          simp only [D]
          congr 1
          congr 1
          exact Finset.sum_congr rfl (fun c hc => by
            rw [Finset.mem_erase] at hc
            rw [hagree c hc.1])
        · -- Degree bound
          intro cs
          exact natDegree_linear_poly_le _ _
    _ = Fintype.card F ^ (m - 1) := by ring

-- ============================================================
-- Section 4: Probabilistic soundness — quadratic test
-- ============================================================

/-- **Probabilistic quadratic test soundness**: if some quadratic constraint
    is violated, the single-challenge test passes on at most
    `|F|^(q-1)` challenge vectors out of `|F|^q` total.

    This gives a soundness error of `1/|F|`.

    Proof idea: from `h_viol`, extract a violated constraint `i_0` with
    `quadError w (qcs i_0) != 0`. The acceptance condition
    `sum_i u[i] * quadError[i] = 0` is a degree-1 polynomial in `u[i_0]`
    with nonzero leading coefficient. By the same fiber argument as the
    linear test, the count is at most `|F|^(q-1)`. -/
noncomputable def quadTest_prob_soundness {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ ∀ i, satisfiesQuad w (qcs i)) :
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
      Fintype.card F ^ (q - 1) := by
  -- Extract a violated constraint i₀
  obtain ⟨i₀, hi₀⟩ := quadTest_violated_exists w qcs h_viol
  have h_err_ne : quadError w (qcs i₀) ≠ 0 := by
    intro h; apply hi₀; unfold quadError at h; exact sub_eq_zero.mp h
  have h_rewrite : ∀ u, quadTestSingleChallenge w qcs u ↔
      ∑ i : Fin q, u i * quadError w (qcs i) = 0 :=
    fun u => quadTestSingle_iff_error_zero w qcs u
  suffices h : countSat (fun u : Fin q → F =>
      ∑ i : Fin q, u i * quadError w (qcs i) = 0) ≤
        Fintype.card F ^ (q - 1) by
    calc countSat (fun u => quadTestSingleChallenge w qcs u)
        ≤ countSat (fun u => ∑ i : Fin q, u i * quadError w (qcs i) = 0) := by
          unfold countSat
          apply Finset.card_le_card
          intro u h_mem
          rw [Finset.mem_filter] at h_mem ⊢
          exact ⟨h_mem.1, (h_rewrite u).mp h_mem.2⟩
      _ ≤ Fintype.card F ^ (q - 1) := h
  let D : (Fin q → F) → Polynomial F := fun u =>
    Polynomial.C (quadError w (qcs i₀)) * Polynomial.X +
    Polynomial.C (∑ i ∈ Finset.univ.erase i₀, u i * quadError w (qcs i))
  have h_eval : ∀ u, (D u).eval (u i₀) =
      ∑ i : Fin q, u i * quadError w (qcs i) := by
    intro u
    simp only [D, eval_add, eval_mul, eval_C, eval_X]
    rw [← Finset.add_sum_erase Finset.univ (fun i => u i * quadError w (qcs i))
          (Finset.mem_univ i₀)]
    ring
  have h_D_ne : ∀ u, D u ≠ 0 := by
    intro u h_eq
    have : (D u).coeff 1 = 0 := by rw [h_eq]; simp
    simp only [D, coeff_add, coeff_C_mul, coeff_X, mul_one, coeff_C, Nat.one_ne_zero,
               ↓reduceIte, add_zero] at this
    exact h_err_ne this
  have h_equiv : ∀ u, (∑ i : Fin q, u i * quadError w (qcs i) = 0) ↔
      (D u ≠ 0 ∧ (D u).eval (u i₀) = 0) := by
    intro u
    exact ⟨fun h_sum => ⟨h_D_ne u, by rw [h_eval]; exact h_sum⟩,
           fun ⟨_, h_root⟩ => by rw [h_eval] at h_root; exact h_root⟩
  calc countSat (fun u => ∑ i : Fin q, u i * quadError w (qcs i) = 0)
      ≤ countSat (fun u => D u ≠ 0 ∧ (D u).eval (u i₀) = 0) := by
        unfold countSat
        apply Finset.card_le_card
        intro u h_mem
        rw [Finset.mem_filter] at h_mem ⊢
        exact ⟨h_mem.1, (h_equiv u).mp h_mem.2⟩
    _ ≤ 1 * Fintype.card F ^ (q - 1) := by
        apply countSat_adaptive_root i₀ D
        · intro cs cs' hagree
          simp only [D]
          congr 1
          congr 1
          exact Finset.sum_congr rfl (fun i hi => by
            rw [Finset.mem_erase] at hi
            rw [hagree i hi.1])
        · intro cs
          exact natDegree_linear_poly_le _ _
    _ = Fintype.card F ^ (q - 1) := by ring

-- ============================================================
-- Section 8: Non-interactive soundness (probability bound)
-- ============================================================

/-- **Non-interactive Ligero soundness (linear component)**:
    if the witness violates the linear constraints, the probability
    of the non-interactive linear test passing is at most `1/|F|`.

    Formally: the number of challenge vectors `alpha` for which the
    single-challenge test passes is at most `|F|^(m-1)`. -/
theorem niLigero_linear_soundness {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h_viol : ¬ satisfiesLinear w lcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
      Fintype.card F ^ (m - 1) :=
  linearTest_prob_soundness w lcs h_viol

/-- **Non-interactive Ligero soundness (quadratic component)**:
    if some quadratic constraint is violated, the probability
    of the non-interactive quadratic test passing is at most `1/|F|`. -/
theorem niLigero_quad_soundness {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ ∀ i, satisfiesQuad w (qcs i)) :
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
      Fintype.card F ^ (q - 1) :=
  quadTest_prob_soundness w qcs h_viol
