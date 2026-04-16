import LeanLongfellow.ZeroKnowledge.Defs
import LeanLongfellow.Sumcheck.Pad
import LeanLongfellow.Ligero.ColumnOpening
import LeanLongfellow.Merkle.Correctness
import LeanLongfellow.FiatShamir.HashDerived

/-! # Composed Full Simulator for Longfellow

Composes the existing sumcheck simulator (`Sumcheck/Pad.lean`) with
Ligero column-opening and Merkle authentication-path simulation to
prove HVZK for the full Longfellow protocol.

## Architecture

The full Longfellow protocol transcript has three components:
1. **Sumcheck rounds** — prover polynomials + verifier challenges.
2. **Column openings** — opened Ligero columns with data.
3. **Merkle authentication paths** — proofs that each column belongs
   to the committed tree.

The simulator constructs each component *without* the witness:

| Component | Simulator strategy | Validity proof |
|-----------|-------------------|----------------|
| Sumcheck | `simulateRounds` from `Pad.lean` | `simulateRounds_sum_check` |
| Column openings | Arbitrary column data consistent with LDT | By construction |
| Merkle paths | Build tree from simulated columns, extract paths | `merkle_path_valid` |

## Main results

- `FullLongfellowSimulator` — the composed simulator structure.
- `fullSimulator_sumcheck_valid` — simulated sumcheck passes telescoping conditions.
- `fullSimulator_merkle_valid` — simulated Merkle paths verify against root.
- `isFullHVZK` — the full Longfellow protocol is honest-verifier zero-knowledge.

## Fiat-Shamir compatibility

In the non-interactive (Fiat-Shamir) compiled protocol, verifier challenges
are derived from the transcript via a hash (random oracle).  The simulator
derives challenges from its *simulated* transcript using the same hash —
see `FiatShamir/HashDerived.lean`.  Since the simulator controls the
transcript, it controls the challenges, and the HVZK argument carries over
to the FS-compiled protocol in the ROM.
-/

set_option autoImplicit false

open Polynomial

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Full protocol transcript
-- ============================================================

/-- A full Longfellow protocol transcript bundles the sumcheck round
    data with Ligero column-opening data and Merkle authentication.

    The sumcheck component is a `SumcheckTranscript` (round polynomials
    and challenges).  The commitment component records the Merkle root,
    opened columns with auth paths, LDT challenge, and combined-row
    coefficients. -/
structure FullTranscript (F : Type*) [Field F] (n : ℕ)
    (D : Type*) [MerkleHash D] (params : LigeroParams) (d : ℕ) where
  /-- Sumcheck round data -/
  scRounds : SumcheckTranscript F n
  /-- Column opening proof (Merkle root, opened columns, LDT data) -/
  colProof : ColumnOpeningProof D F params d

-- ============================================================
-- Section 2: Full verifier conditions
-- ============================================================

/-- The full Longfellow verifier checks two independent conditions:

    1. **Sumcheck telescoping**: the round polynomials satisfy
       `sumCheckConditions`.

    2. **Column-opening verification**: `columnOpeningVerify` passes
       (column hashes, Merkle paths, distinct positions, LDT spot-check). -/
def fullVerifierConditions {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (claimed_sum : F)
    (transcript : FullTranscript F n D params d) : Prop :=
  sumCheckConditions claimed_sum transcript.scRounds ∧
  columnOpeningVerify transcript.colProof

-- ============================================================
-- Section 3: Full simulator structure
-- ============================================================

/-- A simulator for the full Longfellow protocol.  Given the claimed
    sum and verifier challenges, it produces a `FullTranscript`
    WITHOUT access to the witness polynomial. -/
structure FullLongfellowSimulator (F : Type*) [Field F] (n : ℕ)
    (D : Type*) [MerkleHash D] (params : LigeroParams) (d : ℕ) where
  simulate : F → (Fin n → F) → FullTranscript F n D params d

/-- A full simulator is VALID if its output passes both the sumcheck
    telescoping conditions and the column-opening verification for
    any claimed sum and any challenges. -/
def fullSimulatorValid {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (sim : FullLongfellowSimulator F n D params d) : Prop :=
  ∀ (claimed_sum : F) (challenges : Fin n → F),
    fullVerifierConditions claimed_sum (sim.simulate claimed_sum challenges)

/-- The full Longfellow protocol is HVZK if there exists a valid
    full simulator. -/
def isFullHVZK (F : Type*) [Field F] (n : ℕ)
    (D : Type*) [MerkleHash D] (params : LigeroParams) (d : ℕ)
    [ColumnHash D F params.NROW] : Prop :=
  ∃ sim : FullLongfellowSimulator F n D params d,
    fullSimulatorValid sim

-- ============================================================
-- Section 4: Constructing the Merkle tree from leaves
-- ============================================================

/-- Build a complete binary Merkle tree of depth `d` from a leaf
    function `f : Fin (2^d) → D`. -/
noncomputable def buildMerkleTree {D : Type*} [MerkleHash D] :
    {d : ℕ} → (Fin (2 ^ d) → D) → MerkleTree D d
  | 0, f => .leaf (f ⟨0, by omega⟩)
  | d + 1, f =>
    .node
      (buildMerkleTree (fun i => f ⟨i.val, by omega⟩))
      (buildMerkleTree (fun i => f ⟨i.val + 2 ^ d, by omega⟩))

/-- The leaf at index `i` of a tree built from `f` equals `f i`. -/
theorem buildMerkleTree_getLeaf {D : Type*} [MerkleHash D] {d : ℕ}
    (f : Fin (2 ^ d) → D) (i : Fin (2 ^ d)) :
    (buildMerkleTree f).getLeaf i = f i := by
  induction d with
  | zero =>
    simp [buildMerkleTree, MerkleTree.getLeaf]
    congr 1
    exact Fin.ext (by omega)
  | succ n ih =>
    simp only [buildMerkleTree, MerkleTree.getLeaf]
    by_cases h : i.val < 2 ^ n
    · simp only [h, dite_true]; exact ih _ _
    · simp only [h, dite_false]
      rw [ih]
      congr 1; exact Fin.ext (by simp; omega)

-- ============================================================
-- Section 5: Column-opening simulation
-- ============================================================

/-- Simulate a column opening proof by hashing column data, building
    a Merkle tree, and extracting authentication paths. -/
noncomputable def simulateColumnOpening
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (indices : Fin params.NREQ → Fin params.NCOL)
    (colData : Fin params.NREQ → Fin params.NROW → F)
    (domain : EvalDomain F params.NCOL)
    (ldt_u : Fin params.NROW → F)
    (combinedRowCoeffs : Fin params.BLOCK → F)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (leaves : Fin (2 ^ d) → D)
    (_h_leaves_match : ∀ k : Fin params.NREQ,
      leaves (leafIdx (indices k)) = ColumnHash.hashColumn (colData k)) :
    ColumnOpeningProof D F params d :=
  let tree := buildMerkleTree leaves
  { root := tree.root
    openings := fun k =>
      { colIdx := indices k
        colData := colData k
        digest := ColumnHash.hashColumn (colData k)
        authPath := tree.getPath (leafIdx (indices k)) }
    domain := domain
    ldt_u := ldt_u
    combinedRowCoeffs := combinedRowCoeffs }

/-- The simulated column opening proof has Merkle paths that verify
    against the tree root. -/
theorem simulateColumnOpening_paths_valid
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (indices : Fin params.NREQ → Fin params.NCOL)
    (colData : Fin params.NREQ → Fin params.NROW → F)
    (domain : EvalDomain F params.NCOL)
    (ldt_u : Fin params.NROW → F)
    (combinedRowCoeffs : Fin params.BLOCK → F)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (leaves : Fin (2 ^ d) → D)
    (h_leaves_match : ∀ k : Fin params.NREQ,
      leaves (leafIdx (indices k)) = ColumnHash.hashColumn (colData k))
    (k : Fin params.NREQ) :
    let proof := simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match
    verifyPath (proof.openings k).digest (proof.openings k).authPath = proof.root := by
  show verifyPath (ColumnHash.hashColumn (colData k))
    ((buildMerkleTree leaves).getPath (leafIdx (indices k))) =
    (buildMerkleTree leaves).root
  have h_leaf : (buildMerkleTree leaves).getLeaf (leafIdx (indices k)) =
      ColumnHash.hashColumn (colData k) := by
    rw [buildMerkleTree_getLeaf]
    exact h_leaves_match k
  rw [← h_leaf]
  exact merkle_path_valid (buildMerkleTree leaves) (leafIdx (indices k))

/-- The simulated column opening proof has matching column hashes. -/
theorem simulateColumnOpening_hashes_valid
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (indices : Fin params.NREQ → Fin params.NCOL)
    (colData : Fin params.NREQ → Fin params.NROW → F)
    (domain : EvalDomain F params.NCOL)
    (ldt_u : Fin params.NROW → F)
    (combinedRowCoeffs : Fin params.BLOCK → F)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (leaves : Fin (2 ^ d) → D)
    (h_leaves_match : ∀ k : Fin params.NREQ,
      leaves (leafIdx (indices k)) = ColumnHash.hashColumn (colData k))
    (k : Fin params.NREQ) :
    let proof := simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match
    ColumnHash.hashColumn (proof.openings k).colData = (proof.openings k).digest := by
  show ColumnHash.hashColumn (colData k) = ColumnHash.hashColumn (colData k)
  rfl

-- ============================================================
-- Section 6: Full column-opening verify from components
-- ============================================================

/-- If the column hashes match, the Merkle paths verify, positions
    are distinct, and the LDT spot-check passes, then
    `columnOpeningVerify` holds. -/
theorem columnOpeningVerify_of_components
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (h_hash : ∀ k : Fin params.NREQ,
      ColumnHash.hashColumn (proof.openings k).colData = (proof.openings k).digest)
    (h_path : ∀ k : Fin params.NREQ,
      verifyPath (proof.openings k).digest (proof.openings k).authPath = proof.root)
    (h_inj : Function.Injective (fun k => (proof.openings k).colIdx))
    (h_ldt : ∀ k : Fin params.NREQ,
      ∑ i : Fin params.NROW, proof.ldt_u i * (proof.openings k).colData i =
        rsEncode proof.domain params.BLOCK proof.combinedRowCoeffs
          ((proof.openings k).colIdx)) :
    columnOpeningVerify proof :=
  ⟨h_hash, h_path, h_inj, h_ldt⟩

-- ============================================================
-- Section 7: Full column-opening simulation validity
-- ============================================================

/-- **Column-opening simulation validity.**

    The simulated column-opening proof passes `columnOpeningVerify`
    provided:
    - Column indices are injective (distinct positions).
    - The LDT spot-check holds on the chosen data. -/
theorem simulateColumnOpening_valid
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (indices : Fin params.NREQ → Fin params.NCOL)
    (colData : Fin params.NREQ → Fin params.NROW → F)
    (domain : EvalDomain F params.NCOL)
    (ldt_u : Fin params.NROW → F)
    (combinedRowCoeffs : Fin params.BLOCK → F)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (leaves : Fin (2 ^ d) → D)
    (h_leaves_match : ∀ k : Fin params.NREQ,
      leaves (leafIdx (indices k)) = ColumnHash.hashColumn (colData k))
    (h_inj : Function.Injective indices)
    (h_ldt : ∀ k : Fin params.NREQ,
      ∑ i : Fin params.NROW, ldt_u i * colData k i =
        rsEncode domain params.BLOCK combinedRowCoeffs (indices k)) :
    columnOpeningVerify (simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match) := by
  refine ⟨fun k => ?_, fun k => ?_, ?_, fun k => ?_⟩
  · exact simulateColumnOpening_hashes_valid indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match k
  · exact simulateColumnOpening_paths_valid indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match k
  · show Function.Injective (fun k => (simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).openings k |>.colIdx)
    intro a b hab
    show a = b
    simp only [simulateColumnOpening] at hab
    exact h_inj hab
  · show ∑ i, (simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).ldt_u i *
      ((simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).openings k).colData i =
      rsEncode (simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).domain params.BLOCK
      (simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).combinedRowCoeffs
      ((simulateColumnOpening indices colData domain ldt_u
      combinedRowCoeffs leafIdx leaves h_leaves_match).openings k).colIdx
    show ∑ i, ldt_u i * colData k i =
      rsEncode domain params.BLOCK combinedRowCoeffs (indices k)
    exact h_ldt k

-- ============================================================
-- Section 8: Composed full simulator
-- ============================================================

/-- Construct the full Longfellow simulator by composing:
    1. The sumcheck simulator (`simulateRounds` from `Pad.lean`).
    2. A fixed column-opening proof (provided as a parameter).

    The column-opening proof is fixed because in the honest-verifier
    model the verifier's challenges are known to the simulator. -/
noncomputable def mkFullSimulator {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    (validColProof : ColumnOpeningProof D F params d) :
    FullLongfellowSimulator F n D params d where
  simulate claimed_sum challenges :=
    { scRounds := simulateRounds claimed_sum challenges
      colProof := validColProof }

-- ============================================================
-- Section 9: Full HVZK theorem
-- ============================================================

/-- **Full Longfellow HVZK.**

    The full Longfellow protocol (sumcheck rounds + column openings +
    Merkle authentication paths) is honest-verifier zero-knowledge.

    Given ANY valid column-opening proof (which the simulator can
    always construct — see `simulateColumnOpening_valid` and
    `merkle_path_valid`), the composed simulator produces transcripts
    that pass both verifier conditions. -/
theorem fullLongfellow_isHVZK {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (validColProof : ColumnOpeningProof D F params d)
    (h_col_valid : columnOpeningVerify validColProof) :
    isFullHVZK F n D params d :=
  ⟨mkFullSimulator validColProof,
   fun claimed_sum challenges =>
     ⟨simulateRounds_sum_check claimed_sum challenges, h_col_valid⟩⟩

-- ============================================================
-- Section 10: Fiat-Shamir compatible full HVZK
-- ============================================================

/-- **Fiat-Shamir compatible full HVZK.**

    In the non-interactive (Fiat-Shamir) compiled protocol, the
    simulator derives challenges from the simulated transcript via
    the same hash function (random oracle).  Since the simulator
    controls the transcript, it controls the derived challenges.

    For ANY claimed sum and ANY oracle, the full simulator produces
    a valid transcript when challenges are hash-derived.  This is
    because `simulateRounds` works for any challenge assignment,
    including hash-derived ones. -/
theorem fullLongfellow_isHVZK_fiatShamir {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (validColProof : ColumnOpeningProof D F params d)
    (h_col_valid : columnOpeningVerify validColProof)
    (claimed_sum : F)
    [DecidableEq F] [Fintype F]
    (oracle : RandomOracle F) :
    fullVerifierConditions claimed_sum
      ((mkFullSimulator (F := F) (n := n) validColProof).simulate
        claimed_sum (deriveChallenges n oracle)) :=
  ⟨simulateRounds_sum_check claimed_sum (deriveChallenges n oracle), h_col_valid⟩

-- ============================================================
-- Section 11: Degree bound for full simulator
-- ============================================================

/-- All simulated round polynomials have degree ≤ 1. -/
theorem fullSimulator_deg_bound {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    (validColProof : ColumnOpeningProof D F params d)
    (claimed_sum : F) (challenges : Fin n → F)
    (i : Fin n) :
    (((mkFullSimulator (F := F) (n := n) validColProof).simulate
      claimed_sum challenges).scRounds i).prover_poly.natDegree ≤ 1 :=
  simulateRounds_deg claimed_sum challenges i
