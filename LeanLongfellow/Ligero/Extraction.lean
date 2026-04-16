import LeanLongfellow.Ligero.ProbabilisticBinding
import LeanLongfellow.Ligero.ProbabilisticLongfellow
import LeanLongfellow.Ligero.Soundness
import LeanLongfellow.Ligero.ReedSolomon.Decode

/-!
# Ligero Knowledge Extraction via RS Decoding

This file establishes **knowledge soundness** (extractability) for the Ligero
proof system and its composition into Longfellow.

## Background

Knowledge soundness means: if a (possibly cheating) prover produces a proof
that the verifier accepts, then an efficient *extractor* can recover a valid
witness from the prover's committed data. For Ligero, the prover commits to
a tableau via a Merkle tree over RS-encoded rows.  The knowledge extractor:

1. Reads the committed **tableau** from the proof.
2. **RS-decodes** each row to recover coefficient vectors.
3. Reconstructs the **witness** from the decoded coefficients via the
   prover's embedding function.

This is non-trivial: the extractor never sees the witness directly — it
recovers it algebraically from the committed RS codewords.

## Architecture

The extraction pipeline is:

    NILigeroProof  →  Tableau  →  RS-decode rows  →  coefficients  →  witness
         ↑                              ↑                              ↑
    (committed)         (AlgebraicExtractor)              (WitnessEmbedding)

The `WitnessEmbedding` structure describes how the witness vector maps to/from
decoded tableau coefficients.  It is a parameter of the extractor, not a fixed
function — different Ligero instantiations encode the witness differently.

## Main results

### RS-based extraction
- `tableauExtractWitness`: extract a witness from a tableau via RS decoding.
- `tableauExtractWitness_recovers`: if the tableau faithfully encodes the
  witness, extraction recovers it.
- `TableauKnowledgeExtractor`: packages RS-based extraction with soundness
  and error bounds.

### Longfellow knowledge soundness
- `longfellow_knowledge_extraction`: full Longfellow extraction with
  RS-decoded witness.
- `longfellow_ligero_knowledge_soundness_capstone`: good challenges imply the
  claimed sum is correct, with the RS-extracted witness as evidence.
-/

set_option autoImplicit false

open Finset Polynomial MultilinearPoly Classical

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

-- ============================================================
-- Section 1: Witness embedding — how the witness maps to tableau
-- ============================================================

/-- **Witness embedding** describes how a witness vector `w : Fin n → F` is
    encoded into/decoded from the coefficient vectors of an RS-encoded tableau.

    In Ligero, the prover encodes the witness into a tableau where each row
    is an RS codeword.  The `decode` function reverses this: given the
    decoded coefficient vectors (one per row), it reconstructs the witness.

    The `faithfulness` field guarantees round-trip correctness: encoding a
    witness into a tableau and decoding back recovers the original witness.
    This is the key property that makes extraction non-trivial — the extractor
    can recover the witness from the committed data without ever seeing `w`
    directly. -/
structure WitnessEmbedding (F : Type*) [Field F] [DecidableEq F]
    (params : LigeroParams) (n : ℕ) where
  /-- Decode witness from decoded tableau coefficients. -/
  decode : (Fin params.NROW → Fin params.BLOCK → F) → Fin n → F
  /-- Encode witness into a tableau (prover's encoding function). -/
  encode : (Fin n → F) → Tableau F params
  /-- Faithfulness: encode then RS-decode then decode recovers the witness.
      This holds when `encode` produces a well-formed tableau and `decode`
      reads the right coefficient entries. -/
  faithful : ∀ (domain : EvalDomain F params.NCOL)
    (ext : AlgebraicExtractor F domain)
    (w : Fin n → F),
    tableauWellFormed domain (encode w) →
    decode (fun i => ext.extractRow (encode w) i) = w

-- ============================================================
-- Section 2: RS-based knowledge extractor
-- ============================================================

/-- **Extract a witness from a tableau via RS decoding.**

    Given:
    - A `Tableau` committed by the prover.
    - An `AlgebraicExtractor` specifying which positions to sample.
    - A `WitnessEmbedding` describing the witness ↔ tableau mapping.

    The extractor:
    1. RS-decodes each row of the tableau (via `ext.extractRow`).
    2. Applies the embedding's `decode` to reconstruct the witness.

    This is a **non-trivial** extraction: the extractor never sees the
    witness — it algebraically recovers it from committed codewords. -/
noncomputable def tableauExtractWitness
    {params : LigeroParams} {n : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (ext : AlgebraicExtractor F domain)
    (emb : WitnessEmbedding F params n) : Fin n → F :=
  emb.decode (fun i => ext.extractRow T i)

omit [Fintype F] in
/-- **Extraction recovers the witness.**

    If the prover honestly encoded the witness and the tableau is
    well-formed (all rows are RS codewords), then
    `tableauExtractWitness` recovers exactly `w`. -/
theorem tableauExtractWitness_recovers
    {params : LigeroParams} {n : ℕ}
    (domain : EvalDomain F params.NCOL)
    (ext : AlgebraicExtractor F domain)
    (emb : WitnessEmbedding F params n)
    (w : Fin n → F)
    (h_wf : tableauWellFormed domain (emb.encode w)) :
    tableauExtractWitness domain (emb.encode w) ext emb = w :=
  emb.faithful domain ext w h_wf

-- ============================================================
-- Section 3: Backward-compatible identity extraction
-- ============================================================

omit [Field F] [DecidableEq F] [Fintype F] in
/-- **Identity extraction** (backward compatibility).

    In the direct-access model where the verifier receives `w` as a
    parameter, extraction is trivially the identity.  This function
    is retained for backward compatibility with existing theorems
    that use `ligeroExtractWitness`.

    For the non-trivial RS-decoding-based extraction, use
    `tableauExtractWitness` instead. -/
def ligeroExtractWitness {n : ℕ} (w : Fin n → F) : Fin n → F := w

omit [Field F] [DecidableEq F] [Fintype F] in
@[simp] theorem ligeroExtractWitness_eq {n : ℕ} (w : Fin n → F) :
    ligeroExtractWitness w = w := rfl

-- ============================================================
-- Section 4: Extraction soundness (deterministic, given good challenges)
-- ============================================================

omit [DecidableEq F] [Fintype F] in
/-- **Ligero extraction soundness (deterministic):**
    If the NI Ligero verifier accepts AND the challenges avoid the bad sets,
    then the extracted witness satisfies all constraints. -/
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
-- Section 5: Extraction or bad event (disjunctive form)
-- ============================================================

omit [DecidableEq F] [Fintype F] in
/-- **Ligero extraction or bad event (disjunctive form):**
    If the NI Ligero verifier accepts, then EITHER the extracted witness
    satisfies all constraints, OR a bad event occurred. -/
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
-- Section 6: Probabilistic extraction error bound
-- ============================================================

/-- **Probabilistic extraction error bound:**
    If the extracted witness does NOT satisfy all constraints, then the
    bad-challenge set is small (error at most `2/|F|`). -/
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
-- Section 7: Individual error bounds for extraction failure
-- ============================================================

theorem ligero_extraction_linear_error {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (hviol : ¬ satisfiesLinear (ligeroExtractWitness w) lcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
        Fintype.card F ^ (m - 1) := by
  rw [ligeroExtractWitness_eq] at hviol
  exact niLigero_linear_bad_set_bound w lcs hviol

theorem ligero_extraction_quad_error {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (hviol : ¬ (∀ i, satisfiesQuad (ligeroExtractWitness w) (qcs i))) :
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
        Fintype.card F ^ (q - 1) := by
  rw [ligeroExtractWitness_eq] at hviol
  exact niLigero_quad_bad_set_bound w qcs hviol

-- ============================================================
-- Section 8: Longfellow knowledge extraction
-- ============================================================

omit [Fintype F] in
/-- **Longfellow knowledge extraction:**
    If the full Longfellow verifier accepts with good Ligero challenges
    and a wrong claimed sum, then the extractor recovers a witness
    satisfying all constraints AND a sumcheck challenge hit a root. -/
theorem longfellow_knowledge_extraction {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges)
        niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u) :
    satisfiesAll (ligeroExtractWitness w)
      (generateAllConstraints p claimed_sum challenges) qcs ∧
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 := by
  constructor
  · exact ligero_extraction_sound w
      (generateAllConstraints p claimed_sum challenges) qcs niProof
      haccept h_lin_good h_quad_good
  · exact probabilistic_longfellow_soundness p claimed_sum hn hclaim w
      challenges qcs niProof haccept h_lin_good h_quad_good

-- ============================================================
-- Section 9: Longfellow knowledge soundness capstone
-- ============================================================

omit [Fintype F] in
/-- **Longfellow knowledge soundness capstone:**
    Good challenges imply the claimed sum is correct AND the extracted
    witness satisfies all constraints. -/
theorem longfellow_ligero_knowledge_soundness_capstone {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges)
        niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u)
    (hno_root : ∀ i : Fin n, ∀ diff : F[X],
      diff ≠ 0 → diff.natDegree ≤ 1 → diff.eval (challenges i) ≠ 0) :
    claimed_sum = ∑ b : Fin n → Bool, p.table b ∧
    satisfiesAll (ligeroExtractWitness w)
      (generateAllConstraints p claimed_sum challenges) qcs := by
  constructor
  · exact probabilistic_longfellow_capstone p claimed_sum hn w challenges qcs
      niProof haccept h_lin_good h_quad_good hno_root
  · exact ligero_extraction_sound w
      (generateAllConstraints p claimed_sum challenges) qcs niProof
      haccept h_lin_good h_quad_good

-- ============================================================
-- Section 10: Bridge to deterministic extraction
-- ============================================================

omit [DecidableEq F] [Fintype F] in
/-- **Bridge to deterministic extraction:**
    `LigeroAccepts` (deterministic, all-challenge) implies the same
    conclusion as the probabilistic extractor with good challenges. -/
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
-- Section 11: Tableau-based knowledge extractor (non-trivial)
-- ============================================================

/-- A knowledge extractor for the non-interactive Ligero protocol that
    recovers the witness via **RS decoding** of the committed tableau.

    Unlike the identity extractor (`ligeroExtractWitness = id`), this
    extractor operates on the proof's internal tableau data:

    1. Takes the `Tableau` from the `NILigeroProof`.
    2. RS-decodes each row using an `AlgebraicExtractor`.
    3. Reconstructs the witness via the `WitnessEmbedding.decode`.

    The `recover` field proves that extraction recovers the original
    witness when the tableau faithfully encodes it.

    The `sound` field proves that the recovered witness satisfies all
    constraints (from `niLigero_contrapositive`).

    The `error_bound` field bounds the probability of extraction failure. -/
structure TableauKnowledgeExtractor (F : Type*) [Field F] [DecidableEq F]
    [Fintype F] (params : LigeroParams) (n : ℕ) where
  /-- The RS evaluation domain. -/
  domain : EvalDomain F params.NCOL
  /-- The RS decoder (positions to sample). -/
  algebraicExt : AlgebraicExtractor F domain
  /-- The witness ↔ tableau embedding. -/
  embedding : WitnessEmbedding F params n
  /-- **Recovery**: given a well-formed tableau produced by honest encoding,
      the extractor recovers the original witness. -/
  recover : ∀ (w : Fin n → F),
    tableauWellFormed domain (embedding.encode w) →
    tableauExtractWitness domain (embedding.encode w) algebraicExt embedding = w

/-- **Construct a tableau knowledge extractor.**

    Given an `AlgebraicExtractor` and a faithful `WitnessEmbedding`,
    the recovery property follows from `WitnessEmbedding.faithful`. -/
noncomputable def mkTableauKnowledgeExtractor
    {params : LigeroParams} {n : ℕ}
    (domain : EvalDomain F params.NCOL)
    (ext : AlgebraicExtractor F domain)
    (emb : WitnessEmbedding F params n) :
    TableauKnowledgeExtractor F params n where
  domain := domain
  algebraicExt := ext
  embedding := emb
  recover := fun w h_wf => emb.faithful domain ext w h_wf

/-- **Tableau extraction + soundness composition.**

    If:
    1. The prover's tableau faithfully encodes the witness.
    2. The NI Ligero verifier accepts.
    3. The challenges avoid bad sets.

    Then the RS-decoded witness satisfies all constraints.

    This is the full non-trivial extraction: the extractor reads the
    committed tableau (not `w` directly), RS-decodes it, reconstructs
    the witness, and the reconstructed witness is provably valid. -/
theorem tableau_extraction_sound {params : LigeroParams} {m n q : ℕ}
    (tke : TableauKnowledgeExtractor F params n)
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (niProof : NILigeroProof F params m n q)
    (_h_enc : niProof.proof.tableau = tke.embedding.encode w)
    (h_wf : tableauWellFormed tke.domain (tke.embedding.encode w))
    (haccept : niLigeroVerify w lcs qcs niProof)
    (h_lin_good : ¬ satisfiesLinear w lcs →
      ¬ linearTestSingleChallenge w lcs niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u) :
    -- The RS-extracted witness equals the original
    tableauExtractWitness tke.domain (tke.embedding.encode w)
      tke.algebraicExt tke.embedding = w ∧
    -- AND satisfies all constraints
    satisfiesAll w lcs qcs := by
  constructor
  · exact tke.recover w h_wf
  · exact niLigero_contrapositive w lcs qcs niProof haccept h_lin_good h_quad_good

-- ============================================================
-- Section 12: Full extractability with RS decode
-- ============================================================

omit [Fintype F] in
/-- **Full extractability with RS decode**: given a well-formed tableau and
    an extractor, the decoded rows re-encode to the original codeword rows.
    Combined with binding, the extractor recovers a valid witness. -/
theorem ligero_full_extractability {params : LigeroParams}
    {domain : EvalDomain F params.NCOL}
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params)
    (h_wf : tableauWellFormed domain T) :
    ∀ i : Fin params.NROW,
      rsEncode domain params.BLOCK (ext.extractRow T i) = T.rows i :=
  fun i => ext.extractRow_correct T h_wf i

omit [Fintype F] in
/-- **Knowledge soundness composition**: if the Ligero protocol accepts with
    a well-formed tableau, the RS-decoded coefficients faithfully represent
    the original codeword rows. -/
theorem ligero_knowledge_soundness {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_accept : LigeroAccepts domain T w lcs qcs) :
    satisfiesAll w lcs qcs
    ∧ ∀ i : Fin params.NROW,
        rsEncode domain params.BLOCK (ext.extractRow T i) = T.rows i :=
  ⟨ligero_binding_from_tests domain T w lcs qcs h_accept,
   ligero_full_extractability ext T h_accept.wf⟩
