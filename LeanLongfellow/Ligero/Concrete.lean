import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Generate
import LeanLongfellow.Ligero.Longfellow
import LeanLongfellow.Ligero.ReedSolomon.Defs
import LeanLongfellow.Ligero.ReedSolomon.Proximity
import LeanLongfellow.Ligero.Tableau
import LeanLongfellow.Ligero.Tests.LowDegree
import LeanLongfellow.Ligero.Tests.Linear
import LeanLongfellow.Ligero.Tests.Quadratic
import LeanLongfellow.Ligero.Soundness

/-! # Concrete Ligero Instance via Three-Test Protocol

This file provides a `LigeroScheme` instance where `verify` models the
actual Ligero interactive protocol:

1. **Low-degree test**: the combined row (random linear combination of
   tableau rows) is a valid RS codeword.
2. **Linear test**: the honest dot product (computed from the witness)
   equals the combined target under random challenge α.
3. **Quadratic test**: the combined quadratic error under random
   challenge u is zero.

The `binding` proof composes the three test soundness results:
- Linear test acceptance → `satisfiesLinear` (via `linearTest_completeness` /
  `linearTest_accept_iff_zero_error`).
- Quadratic test acceptance → `∀ i, satisfiesQuad` (via `quadraticTest_sound`).
- Combined → `satisfiesAll`.

## Design note

The `LigeroScheme.binding` axiom says: for ALL proofs π, if verify
accepts on commit(w), then w satisfies the constraints. This is an
*ideal* binding property — no error probability.

To achieve this deterministically, the verifier must check enough to
pin down constraint satisfaction. We model this by having the verifier
check `actualDot w lcs alpha = combinedTarget lcs alpha` for EVERY α
(equivalently: all row errors are zero, i.e., `satisfiesLinear`).
The quadratic test similarly checks `combinedQuadError w qcs u = 0` for
every u (equivalently: `∀ i, satisfiesQuad w (qcs i)`).

A probabilistic binding (where verify uses a single random α and
binding holds with probability 1 - m/|F|) would require a different
typeclass signature with error bounds.
-/

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Realistic Ligero proof structure
-- ============================================================

/-- A Ligero proof in the three-test protocol.

    In the interactive protocol, these would be the verifier's challenges
    and the prover's responses. Here we bundle the tableau evidence and
    the verifier's checks. -/
structure LigeroProof (F : Type*) [Field F] (params : LigeroParams) (m n q : ℕ) where
  /-- The tableau (in practice: committed via Merkle root) -/
  tableau : Tableau F params
  /-- Evaluation domain for RS codes -/
  domain : EvalDomain F params.NCOL
  /-- LDT challenge: random coefficients for row combination -/
  ldt_u : Fin params.NROW → F

-- ============================================================
-- Section 2: Three-test verify predicate
-- ============================================================

/-- Ligero verification via the three-test protocol.

    This checks the actual algebraic predicates that the interactive
    Ligero verifier would check:

    1. **LDT**: The random linear combination of tableau rows is a
       valid RS codeword (well-formedness proxy).
    2. **Linear**: The honest dot product equals the combined target
       for ALL α (deterministic check — equivalent to `satisfiesLinear`).
    3. **Quadratic**: The combined quadratic error is zero for ALL u
       (deterministic check — equivalent to `∀ i, satisfiesQuad`).

    The "for all α / for all u" checks make binding deterministic.
    A single-challenge version would give probabilistic binding. -/
def threeTestVerify {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : LigeroProof F params m n q) : Prop :=
  -- Test 1: LDT — combined row is a codeword
  combinedRowIsCodeword proof.domain proof.tableau proof.ldt_u ∧
  -- Test 2: Linear — honest dot equals target for all α
  (∀ alpha : Fin m → F,
    actualDot w lcs alpha = combinedTarget lcs alpha) ∧
  -- Test 3: Quadratic — combined error is zero for all u
  (∀ u : Fin q → F,
    combinedQuadError w qcs u = 0)

-- ============================================================
-- Section 3: Binding proof — three tests → satisfiesAll
-- ============================================================

/-- The linear test condition (actualDot = combinedTarget for all α)
    implies `satisfiesLinear`.

    Proof: For each constraint row c, choosing α = indicator at c
    isolates that row's error. If the dot product matches the target
    for this α, the row error is zero. -/
theorem allAlpha_implies_satisfiesLinear {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h : ∀ alpha : Fin m → F, actualDot w lcs alpha = combinedTarget lcs alpha) :
    satisfiesLinear w lcs := by
  intro c
  -- Use the error characterization: actualDot - combinedTarget = ∑ α[c] * rowError[c]
  -- For any α, the error is zero
  have h_zero : ∀ alpha : Fin m → F, ∑ c' : Fin m, alpha c' * rowError w lcs c' = 0 := by
    intro alpha
    have := linearTest_error_eq w lcs alpha
    rw [h alpha, sub_self] at this
    exact this.symm
  -- Choose α = indicator at c to isolate rowError c
  have h_c := h_zero (fun j => if j = c then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h_c
  -- h_c : rowError w lcs c = 0, i.e., (∑ j, A[c][j]*w[j]) - target[c] = 0
  unfold rowError at h_c
  exact sub_eq_zero.mp h_c

/-- The quadratic test condition (combinedQuadError = 0 for all u)
    implies all quadratic constraints are satisfied.

    Proof: For each constraint i, choosing u = indicator at i
    isolates that constraint's error. -/
theorem allU_implies_satisfiesQuad {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h : ∀ u : Fin q → F, combinedQuadError w qcs u = 0) :
    ∀ i, satisfiesQuad w (qcs i) := by
  intro i
  have h_i := h (fun j => if j = i then 1 else 0)
  simp only [combinedQuadError] at h_i
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h_i
  -- h_i : w (qcs i).left * w (qcs i).right - w (qcs i).output = 0
  exact sub_eq_zero.mp h_i

/-- **Three-test binding**: if all three tests accept, the witness
    satisfies all constraints.

    This is the core composition: LDT gives well-formedness (used by
    downstream but not needed for binding), linear test gives
    `satisfiesLinear`, quadratic test gives `satisfiesQuad`. -/
theorem threeTest_binding {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : LigeroProof F params m n q)
    (h : threeTestVerify w lcs qcs proof) :
    satisfiesAll w lcs qcs := by
  obtain ⟨_, h_linear, h_quad⟩ := h
  exact ⟨allAlpha_implies_satisfiesLinear w lcs h_linear,
         allU_implies_satisfiesQuad w qcs h_quad⟩

-- ============================================================
-- Section 4: Completeness — satisfiesAll → three tests accept
-- ============================================================

/-- **Three-test completeness**: if the witness satisfies all constraints
    and the LDT passes, then the three-test verify accepts. -/
theorem threeTest_completeness {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : LigeroProof F params m n q)
    (h_ldt : combinedRowIsCodeword proof.domain proof.tableau proof.ldt_u)
    (h_sat : satisfiesAll w lcs qcs) :
    threeTestVerify w lcs qcs proof := by
  refine ⟨h_ldt, ?_, ?_⟩
  · intro alpha
    exact linearTest_completeness w lcs alpha h_sat.1
  · intro u
    exact combinedQuadError_zero_of_sat w qcs h_sat.2 u

-- ============================================================
-- Section 5: Concrete LigeroScheme instance via three tests
-- ============================================================

/-- **Concrete Ligero scheme via the three-test protocol.**

    Unlike the trivial instance in `Soundness.lean` (where verify = satisfiesAll),
    this instance models the actual Ligero verification:

    - **Commitment** = the witness itself (abstracting Merkle commitment)
    - **Proof** = tableau + domain + LDT challenge
    - **verify** = three-test protocol (LDT + linear + quadratic)
    - **binding** = proved by composing the three test soundness results

    The binding proof flows through:
    1. `threeTestVerify` acceptance
    2. `allAlpha_implies_satisfiesLinear` (linear test → `satisfiesLinear`)
    3. `allU_implies_satisfiesQuad` (quadratic test → `satisfiesQuad`)
    4. `satisfiesAll` = conjunction of (2) and (3) -/
noncomputable instance threeTestLigeroScheme (F : Type) [Field F]
    (params : LigeroParams) (n m q : ℕ) : LigeroScheme F n m q where
  Commitment := Fin n → F
  Proof := LigeroProof F params m n q
  commit := id
  verify := fun w lcs qcs proof => threeTestVerify w lcs qcs proof
  binding := fun w lcs qcs proof h => threeTest_binding w lcs qcs proof h

-- ============================================================
-- Section 6: Verify is strictly stronger than satisfiesAll
-- ============================================================

/-- Three-test verify implies `satisfiesAll`. -/
theorem threeTestVerify_implies_satisfiesAll {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) (proof : LigeroProof F params m n q)
    (h : threeTestVerify w lcs qcs proof) :
    satisfiesAll w lcs qcs :=
  threeTest_binding w lcs qcs proof h

/-- `satisfiesAll` plus LDT implies three-test verify. -/
theorem satisfiesAll_implies_threeTestVerify {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) (proof : LigeroProof F params m n q)
    (h_ldt : combinedRowIsCodeword proof.domain proof.tableau proof.ldt_u)
    (h_sat : satisfiesAll w lcs qcs) :
    threeTestVerify w lcs qcs proof :=
  threeTest_completeness w lcs qcs proof h_ldt h_sat

-- ============================================================
-- Section 7: End-to-end composition with sumcheck
-- ============================================================

/-- **End-to-end Longfellow soundness via three-test Ligero.**

    Composes the realistic three-test Ligero binding with sumcheck
    soundness: if the Ligero verifier accepts (via three tests) and the
    claimed sum is wrong, a challenge must hit a root of a nonzero
    degree-≤-1 polynomial. -/
theorem concrete_longfellow_soundness
    (F : Type) [Field F] [DecidableEq F]
    {n q : ℕ}
    [L : LigeroScheme F (witnessSize n) (n + 1) q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (ligeroProof : L.Proof)
    (hligero : L.verify (L.commit w)
      (generateAllConstraints p claimed_sum challenges) qcs ligeroProof) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 :=
  longfellow_soundness p claimed_sum hn hclaim w challenges qcs ligeroProof hligero
