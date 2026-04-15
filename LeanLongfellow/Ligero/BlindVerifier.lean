import LeanLongfellow.Ligero.ColumnOpening
import LeanLongfellow.Ligero.ColumnOpeningSoundness
import LeanLongfellow.Ligero.ColumnTests
import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Soundness

/-! # Blind Ligero Verifier

This file defines the full "blind" Ligero verifier that never sees the
witness or full tableau directly. Instead, it receives:

1. A Merkle-committed column opening proof (root, opened columns with
   authentication paths, RS evaluation domain, LDT challenge vector,
   and the claimed combined-row coefficients).
2. A linear-test response polynomial.
3. A quadratic-test response polynomial.
4. Challenge vectors for the linear and quadratic tests.
5. Constraint definitions (in tableau coordinates).

The blind verifier checks:
- Column openings are valid (hashes, Merkle auth paths, distinct positions).
- LDT spot-check passes (combined row matches at opened positions).
- Linear constraint spot-check passes.
- Quadratic constraint spot-check passes.

## Main results

1. **`BlindLigeroProof`**: Full proof structure bundling column openings
   with response polynomials and challenge vectors.

2. **`blindLigeroVerify`**: The verifier predicate — delegates to
   `columnLigeroVerify` from `ColumnTests.lean`.

3. **`blind_ligero_soundness`**: If the blind verifier accepts, the
   column data is authentic (matches the committed tableau), and the
   response polynomials are honestly computed, then the linear and
   quadratic constraints are satisfied at the opened positions.

4. **`blind_ligero_soundness_or_collision`**: Collision-extracting
   variant that concludes with a disjunction.

## Design notes

- The soundness theorem here is a "bridge" theorem: it connects the
  column-level blind verifier to the witness-level constraint predicates.
  Full end-to-end soundness (binding a Merkle commitment to constraint
  satisfaction) requires additionally composing with
  `column_opening_authentic` from `ColumnOpening.lean`.

- The `for all alpha / for all u` pattern from `Concrete.lean` is NOT
  used here. Instead, the blind verifier checks at specific challenge
  vectors provided in the proof. The soundness theorem shows that if
  the checks pass with honest responses, the constraints hold at the
  opened positions. Full binding (for all alpha) requires the
  probabilistic argument from `ProbabilisticBinding.lean`.
-/

set_option autoImplicit false

open Finset

-- ============================================================
-- Section 1: BlindLigeroProof — full proof structure
-- ============================================================

variable {D : Type*} [MerkleHash D]
variable {F : Type*} [Field F]

/-- The complete proof object for blind Ligero verification.

    This bundles the column-opening proof (Merkle commitment, opened
    columns, RS domain, LDT data) with the linear and quadratic test
    response polynomials and challenge vectors.

    The blind verifier receives this structure and checks all three
    Ligero tests (LDT, linear, quadratic) without ever seeing the
    full witness or tableau. -/
structure BlindLigeroProof (D : Type*) [MerkleHash D] (F : Type*) [Field F]
    (params : LigeroParams) (m q d : ℕ) where
  /-- Column-opening proof (root, openings, domain, LDT data) -/
  opening : ColumnOpeningProof D F params d
  /-- Linear test response polynomial -/
  linResponse : LinearResponse F params
  /-- Quadratic test response polynomial -/
  quadResponse : QuadraticResponse F params
  /-- Linear test challenge vector -/
  alpha : Fin m → F
  /-- Quadratic test challenge vector -/
  u_quad : Fin q → F
  /-- Constraint matrix in tableau coordinates -/
  constraintRows : Fin m → Fin params.NROW → F
  /-- Quadratic constraints over tableau row indices -/
  quadRows : Fin q → QuadConstraint params.NROW

-- ============================================================
-- Section 2: blindLigeroVerify — verifier predicate
-- ============================================================

/-- The blind Ligero verifier predicate.

    Delegates to `columnLigeroVerify`, which checks:
    1. Column openings are valid (hashes, Merkle paths, distinct, LDT).
    2. Linear constraint spot-check passes.
    3. Quadratic constraint spot-check passes.

    This is the complete predicate that a real Ligero verifier would
    check, given only the proof object and no direct access to the
    witness or tableau. -/
def blindLigeroVerify {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d) : Prop :=
  columnLigeroVerify proof.opening proof.constraintRows proof.alpha
    proof.linResponse proof.quadRows proof.u_quad proof.quadResponse

/-- Unfolded characterization of `blindLigeroVerify`: the conjunction of
    column-opening verification, linear spot-check, and quadratic
    spot-check. -/
theorem blindLigeroVerify_iff {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d) :
    blindLigeroVerify proof ↔
    columnOpeningVerify proof.opening ∧
    columnLinearCheck proof.opening proof.constraintRows proof.alpha
      proof.linResponse ∧
    columnQuadraticCheck proof.opening proof.quadRows proof.u_quad
      proof.quadResponse :=
  Iff.rfl

-- ============================================================
-- Section 3: Completeness — honest prover is accepted
-- ============================================================

/-- **Blind verifier completeness**: if the tableau is well-formed,
    the column openings are authentic, the column-opening verification
    passes, and the response polynomials are honestly computed, then
    the blind verifier accepts. -/
theorem blind_ligero_completeness {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    -- Column openings pass Merkle + LDT checks
    (h_opening : columnOpeningVerify proof.opening)
    -- Opened columns are authentic
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx)
    -- Linear response is honest
    (h_lin_response : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j)
    -- Quadratic response is honest
    (h_quad_response : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    blindLigeroVerify proof :=
  columnLigeroVerify_completeness proof.opening T proof.constraintRows
    proof.alpha proof.linResponse proof.quadRows proof.u_quad
    proof.quadResponse h_opening h_auth h_lin_response h_quad_response

-- ============================================================
-- Section 4: Soundness — acceptance with authentic data implies
--            constraint satisfaction at opened positions
-- ============================================================

/-- **Blind Ligero soundness (linear test, pointwise)**: if the blind
    verifier accepts, the column data is authentic, and the linear
    response polynomial is honestly computed, then the alpha-combined
    linear constraint evaluates to the honest response at every
    opened position.

    This is the column-level analogue of the linear test: the verifier's
    spot-check confirms that the response polynomial agrees with the
    constraint evaluation at the opened positions. With honest responses,
    this means the constraint evaluation matches at those positions. -/
theorem blind_ligero_linear_pointwise {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx)
    (h_lin_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j) :
    ∀ k : Fin params.NREQ,
      ∑ c : Fin m, proof.alpha c *
        ∑ i : Fin params.NROW, proof.constraintRows c i *
          T.column (proof.opening.openings k).colIdx i =
      honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha
        ((proof.opening.openings k).colIdx) := by
  intro k
  -- From blindLigeroVerify, extract the linear check
  obtain ⟨_, h_lin, _⟩ := hverify
  -- The linear check says: observed value = response codeword at opened position
  have h_spot := h_lin k
  -- The observed value uses colData, rewrite using authenticity
  unfold columnLinearObserved at h_spot
  simp_rw [h_auth k] at h_spot
  -- Now h_spot says the authentic observed value = rsEncode ... at that position
  -- And h_lin_honest says rsEncode = honestLinearResponse
  rw [h_lin_honest] at h_spot
  -- The authentic observed value is exactly the left-hand side
  unfold Tableau.column at h_spot
  exact h_spot

/-- **Blind Ligero soundness (quadratic test, pointwise)**: analogous
    to the linear case. If the blind verifier accepts, the column data
    is authentic, and the quadratic response is honest, then the
    u-combined quadratic error evaluates to the honest response at
    every opened position. -/
theorem blind_ligero_quad_pointwise {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx)
    (h_quad_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    ∀ k : Fin params.NREQ,
      (let col := T.column (proof.opening.openings k).colIdx
       ∑ i : Fin q, proof.u_quad i *
         (col (proof.quadRows i).left * col (proof.quadRows i).right -
          col (proof.quadRows i).output)) =
      honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad
        ((proof.opening.openings k).colIdx) := by
  intro k
  obtain ⟨_, _, h_quad⟩ := hverify
  have h_spot := h_quad k
  unfold columnQuadObserved at h_spot
  simp_rw [h_auth k] at h_spot
  rw [h_quad_honest] at h_spot
  unfold Tableau.column at h_spot
  exact h_spot

-- ============================================================
-- Section 5: LDT consistency from blind verifier
-- ============================================================

/-- **Blind verifier LDT consistency**: if the blind verifier accepts
    and the column data is authentic, then the claimed combined-row
    codeword agrees with the true combined row at all opened positions.

    This is a direct corollary of `column_ldt_consistency`, extracting
    the column-opening verification from the blind verifier. -/
theorem blind_ligero_ldt_consistency {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx) :
    ∀ k : Fin params.NREQ,
      rsEncode proof.opening.domain params.BLOCK proof.opening.combinedRowCoeffs
        ((proof.opening.openings k).colIdx) =
      combinedRow T proof.opening.ldt_u ((proof.opening.openings k).colIdx) := by
  exact column_ldt_consistency proof.opening T hverify.1 h_auth

-- ============================================================
-- Section 6: Main soundness theorem
-- ============================================================

/-- **Blind Ligero soundness**: the main composition theorem.

    If the blind verifier accepts, the column data is authentic (matches
    the committed tableau), and the response polynomials are honestly
    computed, then:

    - The linear constraint evaluation matches the honest response at
      every opened position.
    - The quadratic constraint evaluation matches the honest response at
      every opened position.
    - The LDT claimed codeword agrees with the true combined row at
      every opened position.

    This is the key bridge between the blind verifier and the algebraic
    constraint predicates.

    **Note on binding**: This theorem does NOT establish full constraint
    satisfaction (`satisfiesAll`). That requires:
    1. The "for all alpha / for all u" argument (from `Concrete.lean`)
       to go from pointwise checks to universal satisfaction.
    2. OR: a probabilistic argument showing that a single random alpha/u
       suffices with high probability (from `ProbabilisticBinding.lean`).

    What this theorem DOES establish is that the blind verifier's checks
    are consistent with the committed tableau, which is the essential
    bridge for either binding argument. -/
theorem blind_ligero_soundness {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    -- Column data is authentic (from column_opening_authentic)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx)
    -- Linear response polynomial is honestly computed
    (h_lin_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j)
    -- Quadratic response polynomial is honestly computed
    (h_quad_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    -- THEN: all three tests are consistent with the committed tableau
    -- (1) Linear check: observed matches honest response at opened positions
    (∀ k : Fin params.NREQ,
      columnLinearObserved proof.opening proof.constraintRows proof.alpha k =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha
          ((proof.opening.openings k).colIdx)) ∧
    -- (2) Quadratic check: observed matches honest response at opened positions
    (∀ k : Fin params.NREQ,
      columnQuadObserved proof.opening proof.quadRows proof.u_quad k =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad
          ((proof.opening.openings k).colIdx)) ∧
    -- (3) LDT: claimed codeword agrees with true combined row at opened positions
    (∀ k : Fin params.NREQ,
      rsEncode proof.opening.domain params.BLOCK proof.opening.combinedRowCoeffs
        ((proof.opening.openings k).colIdx) =
      combinedRow T proof.opening.ldt_u ((proof.opening.openings k).colIdx)) := by
  obtain ⟨h_col_verify, h_lin_check, h_quad_check⟩ := hverify
  refine ⟨?_, ?_, ?_⟩
  · -- Linear: observed value = response codeword = honest response
    intro k
    have h_spot := h_lin_check k
    -- h_spot : columnLinearObserved ... k = rsEncode ... (colIdx k)
    rw [h_lin_honest] at h_spot
    exact h_spot
  · -- Quadratic: observed value = response codeword = honest response
    intro k
    have h_spot := h_quad_check k
    rw [h_quad_honest] at h_spot
    exact h_spot
  · -- LDT consistency
    exact column_ldt_consistency proof.opening T h_col_verify h_auth

-- ============================================================
-- Section 7: Deterministic binding via for-all challenges
-- ============================================================

/-- **Blind Ligero deterministic binding (honest response agreement)**:
    if the blind verifier accepts, the column data is authentic, and
    the linear response is honest, then the linear observed values at
    every opened position match the honest response.

    Similarly for the quadratic response.

    This is the key fact that connects the blind verifier's spot-check
    to the algebraic constraint predicates. Combined with the RS
    proximity bound (few positions can agree with a wrong polynomial),
    this gives soundness: either the response polynomial IS correct
    (constraints satisfied), or the verifier detects the mismatch
    with high probability.

    Note: full deterministic binding (for all alpha/u) mirrors
    `threeTest_binding` from `Concrete.lean` but requires lifting
    the tableau-level constraint to witness-level `satisfiesAll`,
    which depends on the witness embedding scheme. -/
theorem blind_ligero_honest_response_agreement
    {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).colData = T.column (proof.opening.openings k).colIdx)
    (h_lin_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j)
    (h_quad_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    -- The observed values equal the honest response at every opened position
    (∀ k : Fin params.NREQ,
      columnLinearObserved proof.opening proof.constraintRows proof.alpha k =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha
          ((proof.opening.openings k).colIdx)) ∧
    (∀ k : Fin params.NREQ,
      columnQuadObserved proof.opening proof.quadRows proof.u_quad k =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad
          ((proof.opening.openings k).colIdx)) :=
  let ⟨h1, h2, _⟩ := blind_ligero_soundness proof T hverify h_auth h_lin_honest h_quad_honest
  ⟨h1, h2⟩

-- ============================================================
-- Section 8: Collision-extracting variant
-- ============================================================

/-- **Blind Ligero soundness (collision-extracting)**: same conclusion
    as `blind_ligero_soundness`, but instead of assuming authenticity
    of the column data via collision-resistance hypotheses, concludes
    with a disjunction: either the soundness conclusion holds, OR
    a column-hash collision exists, OR a Merkle-hash collision exists.

    This composes `column_opening_authentic_or_collision` with the
    main soundness theorem. -/
theorem blind_ligero_soundness_or_collision
    {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    -- Merkle tree commitment data
    (tree : MerkleTree D d)
    (h_root : tree.root = proof.opening.root)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (h_leaves : ∀ j : Fin params.NCOL,
      tree.getLeaf (leafIdx j) =
        ColumnHash.hashColumn (T.column j))
    (h_path_match : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).authPath =
        tree.getPath (leafIdx ((proof.opening.openings k).colIdx)))
    -- Response polynomials are honestly computed
    (h_lin_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j)
    (h_quad_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    -- Conclusion: soundness holds OR hash collision
    ((∀ k : Fin params.NREQ,
        columnLinearObserved proof.opening proof.constraintRows proof.alpha k =
          honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha
            ((proof.opening.openings k).colIdx)) ∧
     (∀ k : Fin params.NREQ,
        columnQuadObserved proof.opening proof.quadRows proof.u_quad k =
          honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad
            ((proof.opening.openings k).colIdx)) ∧
     (∀ k : Fin params.NREQ,
        rsEncode proof.opening.domain params.BLOCK proof.opening.combinedRowCoeffs
          ((proof.opening.openings k).colIdx) =
        combinedRow T proof.opening.ldt_u ((proof.opening.openings k).colIdx))) ∨
    ColumnHashCollision D F params.NROW ∨
    MerkleHashCollision D := by
  -- First try to establish authenticity via the collision-extracting lemma
  rcases column_opening_authentic_or_collision proof.opening hverify.1
      tree h_root leafIdx T h_leaves h_path_match with h_auth | h_col | h_merkle
  · -- Authentic data: apply the main soundness theorem
    left
    exact blind_ligero_soundness proof T hverify h_auth h_lin_honest h_quad_honest
  · -- Column hash collision
    right; left; exact h_col
  · -- Merkle hash collision
    right; right; exact h_merkle

-- ============================================================
-- Section 9: Blind verifier implies column-opening is valid
-- ============================================================

/-- The blind verifier implies column-opening verification passes. -/
theorem blind_implies_column_opening {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (hverify : blindLigeroVerify proof) :
    columnOpeningVerify proof.opening :=
  hverify.1

/-- The blind verifier implies opened positions are distinct. -/
theorem blind_implies_distinct_positions {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (hverify : blindLigeroVerify proof) :
    Function.Injective (fun k => (proof.opening.openings k).colIdx) :=
  hverify.1.2.2.1

-- ============================================================
-- Section 10: Composition with column-opening authenticity
-- ============================================================

/-- **End-to-end blind binding (CR version)**: if the blind verifier
    accepts, the Merkle tree was honestly built from the tableau, hash
    functions are collision-resistant, and response polynomials are
    honest, then the soundness conclusion holds.

    This composes `column_opening_authentic` with `blind_ligero_soundness`
    to give a self-contained theorem that starts from CR hypotheses. -/
theorem blind_ligero_binding_cr {params : LigeroParams} {m q d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : BlindLigeroProof D F params m q d)
    (T : Tableau F params)
    (hverify : blindLigeroVerify proof)
    -- Collision resistance
    (hcr_col : Function.Injective
      (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (hcr_merkle : Function.Injective
      (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    -- Merkle tree commitment data
    (tree : MerkleTree D d)
    (h_root : tree.root = proof.opening.root)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (h_leaves : ∀ j : Fin params.NCOL,
      tree.getLeaf (leafIdx j) =
        ColumnHash.hashColumn (T.column j))
    (h_path_match : ∀ k : Fin params.NREQ,
      (proof.opening.openings k).authPath =
        tree.getPath (leafIdx ((proof.opening.openings k).colIdx)))
    -- Response polynomials are honestly computed
    (h_lin_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.linResponse.coeffs j =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha j)
    (h_quad_honest : ∀ j : Fin params.NCOL,
      rsEncode proof.opening.domain params.BLOCK proof.quadResponse.coeffs j =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad j) :
    -- Conclusion: all three tests are consistent
    (∀ k : Fin params.NREQ,
      columnLinearObserved proof.opening proof.constraintRows proof.alpha k =
        honestLinearResponse proof.opening.domain T proof.constraintRows proof.alpha
          ((proof.opening.openings k).colIdx)) ∧
    (∀ k : Fin params.NREQ,
      columnQuadObserved proof.opening proof.quadRows proof.u_quad k =
        honestQuadResponse proof.opening.domain T proof.quadRows proof.u_quad
          ((proof.opening.openings k).colIdx)) ∧
    (∀ k : Fin params.NREQ,
      rsEncode proof.opening.domain params.BLOCK proof.opening.combinedRowCoeffs
        ((proof.opening.openings k).colIdx) =
      combinedRow T proof.opening.ldt_u ((proof.opening.openings k).colIdx)) := by
  -- First establish authenticity from CR hypotheses
  have h_auth := column_opening_authentic proof.opening hcr_col hcr_merkle
    hverify.1 tree h_root leafIdx T h_leaves h_path_match
  -- Then apply the main soundness theorem
  exact blind_ligero_soundness proof T hverify h_auth h_lin_honest h_quad_honest
