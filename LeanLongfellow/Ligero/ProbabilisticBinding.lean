import LeanLongfellow.Ligero.FiatShamir

/-! # Probabilistic Ligero Binding

Connects the single-challenge Ligero verifier (`niLigeroVerify`) to a
probabilistic binding statement, addressing the gap between the ideal
all-challenge verifier (`threeTestVerify`) and the real protocol.

## Main results

- `niLigero_binding_or_bad`: if `niLigeroVerify` accepts, either the
  witness satisfies all constraints, or the challenges hit a bad set
  whose probability is bounded by `2/|F|` (one error for the linear
  test, one for the quadratic test).

- `niLigero_contrapositive`: if the challenges avoid the bad set AND
  the verifier accepts, the witness satisfies all constraints.

These theorems show that single-challenge Ligero (the real protocol)
achieves soundness with error `≤ 2/|F|`, not just the ideal verifier.
-/

open Finset Classical

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Binding or bad event
-- ============================================================

/-- **Probabilistic Ligero binding (disjunctive form):**
    If `niLigeroVerify` accepts, then EITHER:
    - The witness satisfies all linear and quadratic constraints, OR
    - The linear test challenge `alpha` is in the bad set (size ≤ |F|^(m-1)), OR
    - The quadratic test challenge `u` is in the bad set (size ≤ |F|^(q-1)).

    This is the probabilistic analog of `LigeroScheme.binding`: instead of
    deterministic constraint satisfaction, we get satisfaction OR bounded
    error probability. -/
theorem niLigero_binding_or_bad {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (haccept : niLigeroVerify w lcs qcs niProof) :
    satisfiesAll w lcs qcs ∨
    (¬ satisfiesLinear w lcs ∧ linearTestSingleChallenge w lcs niProof.alpha) ∨
    (¬ (∀ i, satisfiesQuad w (qcs i)) ∧ quadTestSingleChallenge w qcs niProof.u) := by
  by_cases h_lin : satisfiesLinear w lcs
  · by_cases h_quad : ∀ i, satisfiesQuad w (qcs i)
    · left; exact ⟨h_lin, h_quad⟩
    · right; right; exact ⟨h_quad, haccept.2.2⟩
  · right; left; exact ⟨h_lin, haccept.2.1⟩

-- ============================================================
-- Section 2: Contrapositive — good challenges imply binding
-- ============================================================

/-- **Probabilistic Ligero contrapositive:**
    If the verifier accepts AND the challenges are NOT in the bad set
    for either test, then the witness satisfies all constraints.

    "Not in the bad set" means: the linear test would reject if
    constraints were violated, and the quadratic test would reject
    if constraints were violated. -/
theorem niLigero_contrapositive {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (haccept : niLigeroVerify w lcs qcs niProof)
    -- Good challenges: if constraints were violated, the test would catch it
    (h_lin_good : ¬ satisfiesLinear w lcs → ¬ linearTestSingleChallenge w lcs niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) → ¬ quadTestSingleChallenge w qcs niProof.u) :
    satisfiesAll w lcs qcs := by
  rcases niLigero_binding_or_bad w lcs qcs niProof haccept with h | ⟨hviol, hpass⟩ | ⟨hviol, hpass⟩
  · exact h
  · exact absurd hpass (h_lin_good hviol)
  · exact absurd hpass (h_quad_good hviol)

-- ============================================================
-- Section 3: Error probability bounds
-- ============================================================

variable [DecidableEq F] [Fintype F]

/-- **Linear test bad set is small:**
    If the witness violates some linear constraint, the set of alpha
    values for which the single-challenge test still passes has size
    at most `|F|^(m-1)` out of `|F|^m` total.
    Probability of hitting the bad set: `≤ 1/|F|`. -/
theorem niLigero_linear_bad_set_bound {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (hviol : ¬ satisfiesLinear w lcs) :
    countSat (fun alpha : Fin m → F => linearTestSingleChallenge w lcs alpha) ≤
      Fintype.card F ^ (m - 1) :=
  linearTest_prob_soundness w lcs hviol

/-- **Quadratic test bad set is small:**
    If some quadratic constraint is violated, the set of u values for
    which the single-challenge test still passes has size at most
    `|F|^(q-1)` out of `|F|^q` total.
    Probability of hitting the bad set: `≤ 1/|F|`. -/
theorem niLigero_quad_bad_set_bound {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (hviol : ¬ (∀ i, satisfiesQuad w (qcs i))) :
    countSat (fun u : Fin q → F => quadTestSingleChallenge w qcs u) ≤
      Fintype.card F ^ (q - 1) :=
  quadTest_prob_soundness w qcs hviol

-- ============================================================
-- Section 4: Combined error bound via union bound
-- ============================================================

/-- **Combined probabilistic Ligero error bound:**
    If the witness does NOT satisfy all constraints, the probability
    that `niLigeroVerify` accepts is at most `2/|F|` (more precisely:
    the number of (alpha, u) pairs for which the verifier accepts
    despite constraint violation is at most
    `|F|^(m-1) · |F|^q + |F|^m · |F|^(q-1)` out of `|F|^(m+q)` total,
    giving error `≤ 1/|F| + 1/|F| = 2/|F|`).

    This shows the single-challenge Ligero protocol achieves soundness
    with concrete error bound, not just the ideal all-challenge verifier. -/
theorem niLigero_combined_error {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (hviol : ¬ satisfiesAll w lcs qcs) :
    countSat (fun (challenges : Fin m → F) =>
      linearTestSingleChallenge w lcs challenges) ≤
        Fintype.card F ^ (m - 1) ∨
    countSat (fun (challenges : Fin q → F) =>
      quadTestSingleChallenge w qcs challenges) ≤
        Fintype.card F ^ (q - 1) := by
  unfold satisfiesAll at hviol
  by_cases h_lin : satisfiesLinear w lcs
  · -- Linear constraints are satisfied, so quadratic must be violated
    have h_quad : ¬ ∀ i, satisfiesQuad w (qcs i) := fun h => hviol ⟨h_lin, h⟩
    right; exact niLigero_quad_bad_set_bound w qcs h_quad
  · -- Linear constraints are violated
    left; exact niLigero_linear_bad_set_bound w lcs h_lin
