import LeanLongfellow.Ligero.ProbabilisticBinding
import LeanLongfellow.Ligero.ProbabilisticLongfellow
import LeanLongfellow.Ligero.Soundness
import LeanLongfellow.Ligero.ReedSolomon.Decode

/-!
# Ligero Knowledge Extraction

This file establishes **knowledge soundness** (extractability) for the Ligero
proof system and its composition into Longfellow.

## Background

Knowledge soundness means: if a (possibly cheating) prover produces a proof
that the verifier accepts, then an efficient *extractor* can recover a valid
witness from the prover's state. For Ligero, the prover commits to a witness
`w` directly (via a Merkle tree over an RS-encoded tableau), so extraction is
trivial in the idealized model -- the extractor simply reads the committed
values.

The non-trivial content is the *soundness* of extraction: the extracted witness
actually satisfies the constraints. This follows from the probabilistic binding
theorem `niLigero_binding_or_bad` (repackaged via `niLigero_contrapositive`):
if the NI Ligero verifier accepts and the challenges avoid bounded bad sets,
the committed witness satisfies all linear and quadratic constraints.

## Main results

### Ligero extraction
- `ligeroExtractWitness`: the identity extractor (reads the committed witness).
- `ligero_extraction_sound`: if `niLigeroVerify` accepts and challenges avoid
  bad sets, the extracted witness satisfies all constraints.
- `ligero_extraction_or_bad`: disjunctive form -- acceptance implies constraint
  satisfaction OR a bad event with bounded probability.
- `ligero_extraction_error_bound`: if the extracted witness does NOT satisfy
  constraints, the set of bad challenges is small (error at most `2/|F|`).

### Longfellow knowledge soundness
- `longfellow_knowledge_extraction`: if the full Longfellow verifier (NI Ligero
  + sumcheck) accepts with good challenges and a wrong claim, a sumcheck
  challenge hit a polynomial root -- and the extractor recovers the witness.
- `longfellow_knowledge_soundness_capstone`: the full capstone -- good
  challenges imply the claimed sum is correct, with the extracted witness
  as evidence.

## Design notes

The extractor is the identity function because Ligero is a *designated-prover*
scheme where the prover commits to the witness directly. In a real
implementation, the extractor would rewind the prover to extract the Merkle
openings, but in our idealized algebraic model the witness is available.

The `AlgebraicExtractor` in `ReedSolomon/Decode.lean` provides an alternative
RS-decoding-based extractor for the deterministic model. This file focuses on
the probabilistic model with `niLigeroVerify`.
-/

set_option autoImplicit false

open Finset Polynomial MultilinearPoly Classical

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

-- ============================================================
-- Section 1: Knowledge extractor definition
-- ============================================================

omit [Field F] [DecidableEq F] [Fintype F] in
/-- **Knowledge extraction for Ligero:** the committed witness itself is the
    extracted witness. In Ligero, the prover commits to the witness directly
    (via a Merkle tree over the RS-encoded tableau), so extraction is trivial
    in the idealized model -- the extractor reads the committed values.

    The non-trivial content is in the *soundness* of extraction: the extracted
    witness actually satisfies the constraints. This follows from
    `niLigero_binding_or_bad`. -/
def ligeroExtractWitness {n : ℕ} (w : Fin n → F) : Fin n → F := w

omit [Field F] [DecidableEq F] [Fintype F] in
/-- The extractor is the identity: it returns exactly the committed witness. -/
@[simp] theorem ligeroExtractWitness_eq {n : ℕ} (w : Fin n → F) :
    ligeroExtractWitness w = w := rfl

-- ============================================================
-- Section 2: Extraction soundness (deterministic, given good challenges)
-- ============================================================

/-- **Ligero extraction soundness (deterministic):**
    If the NI Ligero verifier accepts AND the challenges avoid the bad sets
    for both the linear and quadratic tests, then the extracted witness
    satisfies all constraints.

    This is a direct repackaging of `niLigero_contrapositive` as a knowledge
    extraction statement. The extractor is the identity, so the theorem says:
    the committed witness itself satisfies all constraints. -/
theorem ligero_extraction_sound {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (haccept : niLigeroVerify w lcs qcs niProof)
    (h_lin_good : ¬ satisfiesLinear w lcs →
      ¬ linearTestSingleChallenge w lcs niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u) :
    satisfiesAll (ligeroExtractWitness w) lcs qcs := by
  rw [ligeroExtractWitness_eq]
  exact niLigero_contrapositive w lcs qcs niProof haccept h_lin_good h_quad_good

-- ============================================================
-- Section 3: Extraction or bad event (disjunctive form)
-- ============================================================

/-- **Ligero extraction or bad event (disjunctive form):**
    If the NI Ligero verifier accepts, then EITHER:
    - The extracted witness satisfies all constraints, OR
    - The linear test challenge hit the bad set, OR
    - The quadratic test challenge hit the bad set.

    This is a direct repackaging of `niLigero_binding_or_bad`. -/
theorem ligero_extraction_or_bad {params : LigeroParams} {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (haccept : niLigeroVerify w lcs qcs niProof) :
    satisfiesAll (ligeroExtractWitness w) lcs qcs ∨
    (¬ satisfiesLinear w lcs ∧ linearTestSingleChallenge w lcs niProof.alpha) ∨
    (¬ (∀ i, satisfiesQuad w (qcs i)) ∧
      quadTestSingleChallenge w qcs niProof.u) := by
  rw [ligeroExtractWitness_eq]
  exact niLigero_binding_or_bad w lcs qcs niProof haccept

-- ============================================================
-- Section 4: Probabilistic extraction error bound
-- ============================================================

/-- **Probabilistic extraction error bound:**
    If the extracted witness does NOT satisfy all constraints, then either
    the linear test bad set or the quadratic test bad set is small:
    - Linear bad set: at most `|F|^(m-1)` out of `|F|^m` challenge vectors
    - Quadratic bad set: at most `|F|^(q-1)` out of `|F|^q` challenge vectors

    Combined error probability: at most `2/|F|`.

    This is a direct repackaging of `niLigero_combined_error`. -/
theorem ligero_extraction_error_bound {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (hviol : ¬ satisfiesAll (ligeroExtractWitness w) lcs qcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
        Fintype.card F ^ (m - 1) ∨
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
        Fintype.card F ^ (q - 1) := by
  rw [ligeroExtractWitness_eq] at hviol
  exact niLigero_combined_error w lcs qcs hviol

-- ============================================================
-- Section 5: Individual error bounds for extraction failure
-- ============================================================

/-- **Linear extraction error bound:**
    If the extracted witness violates some linear constraint, the set of
    alpha values for which the single-challenge test still passes has size
    at most `|F|^(m-1)`. -/
theorem ligero_extraction_linear_error {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (hviol : ¬ satisfiesLinear (ligeroExtractWitness w) lcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
        Fintype.card F ^ (m - 1) := by
  rw [ligeroExtractWitness_eq] at hviol
  exact niLigero_linear_bad_set_bound w lcs hviol

/-- **Quadratic extraction error bound:**
    If the extracted witness violates some quadratic constraint, the set of
    u values for which the single-challenge test still passes has size at
    most `|F|^(q-1)`. -/
theorem ligero_extraction_quad_error {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (hviol : ¬ (∀ i, satisfiesQuad (ligeroExtractWitness w) (qcs i))) :
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
        Fintype.card F ^ (q - 1) := by
  rw [ligeroExtractWitness_eq] at hviol
  exact niLigero_quad_bad_set_bound w qcs hviol

-- ============================================================
-- Section 6: Longfellow knowledge extraction
-- ============================================================

/-- **Longfellow knowledge extraction:**
    If the full Longfellow verifier (NI Ligero + sumcheck) accepts with good
    Ligero challenges and a wrong claimed sum, then:
    1. The extractor recovers the committed witness (identity extraction).
    2. A sumcheck challenge must have hit a root of a nonzero degree-le-1
       polynomial.

    This composes Ligero extraction soundness with sumcheck soundness via
    `probabilistic_longfellow_soundness`. The extracted witness satisfies
    all constraints (by `ligero_extraction_sound`), and the wrong claim
    forces a root hit (by `sumcheck_soundness_det`). -/
theorem longfellow_knowledge_extraction {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    -- NI Ligero accepted
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    -- Good challenges for Ligero tests
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges)
        niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u) :
    -- The extracted witness satisfies all constraints
    satisfiesAll (ligeroExtractWitness w)
      (generateAllConstraints p claimed_sum challenges) qcs ∧
    -- AND a sumcheck challenge hit a polynomial root
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 := by
  constructor
  · exact ligero_extraction_sound w
      (generateAllConstraints p claimed_sum challenges) qcs niProof
      haccept h_lin_good h_quad_good
  · exact probabilistic_longfellow_soundness p claimed_sum hn hclaim w
      challenges qcs niProof haccept h_lin_good h_quad_good

-- ============================================================
-- Section 7: Longfellow knowledge soundness capstone
-- ============================================================

/-- **Longfellow knowledge soundness capstone:**
    If the full Longfellow verifier accepts with good challenges (both Ligero
    and sumcheck), then:
    1. The claimed sum is correct.
    2. The extracted witness satisfies all constraints.

    This is the strongest knowledge soundness statement: good challenges imply
    both correctness and extractability. It composes
    `probabilistic_longfellow_capstone` (for the claimed sum) with
    `ligero_extraction_sound` (for constraint satisfaction). -/
theorem longfellow_knowledge_soundness_capstone {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    -- NI Ligero accepted
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    -- Good challenges for Ligero tests
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges)
        niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u)
    -- No sumcheck challenge hits a polynomial root
    (hno_root : ∀ i : Fin n, ∀ diff : F[X],
      diff ≠ 0 → diff.natDegree ≤ 1 → diff.eval (challenges i) ≠ 0) :
    -- The claimed sum is correct
    claimed_sum = ∑ b : Fin n → Bool, p.table b ∧
    -- AND the extracted witness satisfies all constraints
    satisfiesAll (ligeroExtractWitness w)
      (generateAllConstraints p claimed_sum challenges) qcs := by
  constructor
  · exact probabilistic_longfellow_capstone p claimed_sum hn w challenges qcs
      niProof haccept h_lin_good h_quad_good hno_root
  · exact ligero_extraction_sound w
      (generateAllConstraints p claimed_sum challenges) qcs niProof
      haccept h_lin_good h_quad_good

-- ============================================================
-- Section 8: Connection to deterministic extraction
-- ============================================================

omit [DecidableEq F] [Fintype F] in
/-- **Bridge to deterministic extraction:**
    The probabilistic extraction (this file) and deterministic extraction
    (`ReedSolomon/Decode.lean`) agree: both conclude `satisfiesAll w lcs qcs`
    when the appropriate acceptance condition holds.

    This theorem shows that `LigeroAccepts` (deterministic, all-challenge)
    implies the same conclusion as the probabilistic extractor with good
    challenges. -/
theorem extraction_deterministic_bridge {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_accept : LigeroAccepts domain T w lcs qcs) :
    satisfiesAll (ligeroExtractWitness w) lcs qcs := by
  rw [ligeroExtractWitness_eq]
  exact ligero_binding_from_tests domain T w lcs qcs h_accept

-- ============================================================
-- Section 9: Knowledge extraction as a structure
-- ============================================================

/-- A knowledge extractor for the non-interactive Ligero protocol.
    Packages the extraction function together with its soundness guarantee.

    The `error_bound` field states that when extraction fails (the extracted
    witness does not satisfy constraints), the probability of the verifier
    accepting is bounded. -/
structure NILigeroKnowledgeExtractor (F : Type*) [Field F] [DecidableEq F]
    [Fintype F] (m n q : ℕ) where
  /-- The extraction function: maps a committed witness to an extracted witness. -/
  extract : (Fin n → F) → (Fin n → F)
  /-- Extraction is the identity: the extracted witness IS the committed witness. -/
  extract_eq : ∀ w, extract w = w
  /-- Soundness: if NI Ligero accepts with good challenges, the extracted
      witness satisfies all constraints. -/
  sound : ∀ {params : LigeroParams}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (_haccept : niLigeroVerify w lcs qcs niProof)
    (_h_lin_good : ¬ satisfiesLinear w lcs →
      ¬ linearTestSingleChallenge w lcs niProof.alpha)
    (_h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u),
    satisfiesAll (extract w) lcs qcs
  /-- Error bound: if extraction fails, the bad-challenge set is small. -/
  error_bound : ∀
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (_hviol : ¬ satisfiesAll (extract w) lcs qcs),
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
        Fintype.card F ^ (m - 1) ∨
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
        Fintype.card F ^ (q - 1)

/-- **Canonical NI Ligero knowledge extractor:**
    Constructs the identity-based knowledge extractor with all soundness
    and error bound proofs. -/
noncomputable def niLigeroKnowledgeExtractor (m n q : ℕ) :
    NILigeroKnowledgeExtractor F m n q where
  extract := ligeroExtractWitness
  extract_eq := ligeroExtractWitness_eq
  sound := fun w lcs qcs niProof haccept h_lin_good h_quad_good =>
    ligero_extraction_sound w lcs qcs niProof haccept h_lin_good h_quad_good
  error_bound := fun w lcs qcs hviol =>
    ligero_extraction_error_bound w lcs qcs hviol
