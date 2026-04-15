import LeanLongfellow.Ligero.MerkleCommitment
import LeanLongfellow.Ligero.ReedSolomon.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Column-Opening Game for Ligero

Defines the data structures and predicates for a "blind" Ligero verifier
that only sees opened columns authenticated by Merkle paths — never the
full witness or tableau.

## Motivation

The earlier Ligero verifier (`merkleVerify`, `niLigeroVerify`) takes the
full witness `w : Fin n → F` directly.  A real Ligero verifier only sees
columns opened via Merkle authentication paths.  This module bridges
that gap by defining:

1. `ColumnOpening` — a single opened column with its Merkle proof.
2. `ColumnOpeningProof` — the full proof object the verifier receives.
3. `columnOpeningVerify` — the predicate capturing what the verifier checks.
4. `column_opening_authentic` — if the Merkle root was computed from a
   real tableau, the opened columns must match the committed data
   (assuming collision-resistant hashes).
5. `column_opening_authentic_or_collision` — collision-extracting variant.

## Design choices

- The verifier never sees the full tableau; it only sees `ColumnOpeningProof`.
- Column hash and Merkle hash collision resistance are explicit hypotheses,
  not class fields (following the project convention).
- The `colIdx ↦ Fin (2^d)` mapping is left to the commitment scheme;
  here we only require that opened positions are distinct.
-/

set_option autoImplicit false

open Finset in

-- ============================================================
-- Section 1: ColumnOpening — a single opened column
-- ============================================================

variable {D : Type*} [MerkleHash D]
variable {F : Type*} [Field F]

/-- A single opened column with its Merkle authentication data.

    The verifier receives one of these for each column it requests
    to be opened.  It contains the column data, a column hash
    (Merkle leaf), and an authentication path to the committed root. -/
structure ColumnOpening (D : Type*) [MerkleHash D] (F : Type*) [Field F]
    (params : LigeroParams) (d : ℕ) where
  /-- Which column was opened (index into the tableau) -/
  colIdx : Fin params.NCOL
  /-- The column values — one field element per row -/
  colData : Fin params.NROW → F
  /-- Column digest (the Merkle leaf) -/
  digest : D
  /-- Authentication path from the leaf to the root -/
  authPath : AuthPath D d

-- ============================================================
-- Section 2: ColumnOpeningProof — full proof object
-- ============================================================

/-- The full proof object for column-opening verification.

    The blind verifier receives this instead of the witness.  It
    contains the Merkle root (commitment), the opened columns with
    authentication paths, the RS evaluation domain, the LDT challenge
    vector, and the claimed combined-row coefficients. -/
structure ColumnOpeningProof (D : Type*) [MerkleHash D] (F : Type*) [Field F]
    (params : LigeroParams) (d : ℕ) where
  /-- Merkle root — the commitment -/
  root : D
  /-- Opened columns (one per requested position) -/
  openings : Fin params.NREQ → ColumnOpening D F params d
  /-- Reed-Solomon evaluation domain -/
  domain : EvalDomain F params.NCOL
  /-- LDT challenge vector (one weight per row) -/
  ldt_u : Fin params.NROW → F
  /-- Claimed combined row as RS coefficients -/
  combinedRowCoeffs : Fin params.BLOCK → F

-- ============================================================
-- Section 3: columnOpeningVerify — verifier predicate
-- ============================================================

/-- The column-opening verifier predicate.

    The blind verifier checks four conditions:
    1. **Column hash**: each column's data hashes to its claimed digest.
    2. **Merkle path**: each digest authenticates against the root.
    3. **Distinct positions**: opened column indices are distinct
       (needed for the proximity / distance argument).
    4. **LDT spot-check**: the inner product of the LDT challenge
       with each opened column equals the claimed combined-row
       codeword evaluated at that column's position. -/
def columnOpeningVerify {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d) : Prop :=
  -- 1. Column hashes match digests
  (∀ k : Fin params.NREQ,
    ColumnHash.hashColumn (proof.openings k).colData = (proof.openings k).digest) ∧
  -- 2. All auth paths verify against the root
  (∀ k : Fin params.NREQ,
    verifyPath (proof.openings k).digest (proof.openings k).authPath = proof.root) ∧
  -- 3. Opened positions are distinct
  Function.Injective (fun k => (proof.openings k).colIdx) ∧
  -- 4. LDT spot-check: combined row matches at opened positions
  (∀ k : Fin params.NREQ,
    ∑ i : Fin params.NROW, proof.ldt_u i * (proof.openings k).colData i =
    rsEncode proof.domain params.BLOCK proof.combinedRowCoeffs
      ((proof.openings k).colIdx))

-- ============================================================
-- Section 4: column_opening_authentic — binding theorem
-- ============================================================

/-- **Column opening authenticity**: if the verifier accepts a
    column-opening proof, the Merkle root was computed from a real
    tree whose leaves are column hashes of a tableau, and both hash
    functions are collision-resistant, then the opened column data
    must match the committed tableau.

    Proof sketch:
    1. From `hverify` we get `hashColumn colData = digest` and
       `verifyPath digest authPath = root`.
    2. From `h_leaves` we know the tree contains
       `hashColumn (tableau.column j)` at some leaf position.
    3. If that leaf position has the same auth path, `merkle_binding`
       gives us `digest = hashColumn (tableau.column j)`.
    4. By column-hash injectivity, `colData = tableau.column j`.

    The hypothesis `h_path_match` explicitly ties the opening's auth
    path to the tree's auth path at the mapped position, avoiding the
    need to model the full column-index → leaf-index mapping. -/
theorem column_opening_authentic {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (hcr_col : Function.Injective
      (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (hcr_merkle : Function.Injective
      (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    (hverify : columnOpeningVerify proof)
    -- The tree's root matches the committed root
    (tree : MerkleTree D d)
    (h_root : tree.root = proof.root)
    -- A mapping from column indices to leaf positions
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    -- The tableau whose columns were committed
    (tableau : Tableau F params)
    -- Each column's hash is the corresponding leaf
    (h_leaves : ∀ j : Fin params.NCOL,
      tree.getLeaf (leafIdx j) =
        ColumnHash.hashColumn (tableau.column j))
    -- The opening's auth path matches the tree's path at the mapped position
    (h_path_match : ∀ k : Fin params.NREQ,
      (proof.openings k).authPath =
        tree.getPath (leafIdx ((proof.openings k).colIdx))) :
    ∀ k : Fin params.NREQ,
      (proof.openings k).colData =
        tableau.column (proof.openings k).colIdx := by
  intro k
  obtain ⟨hhash, hpath, _, _⟩ := hverify
  -- Step 1: The opening's column data hashes to its digest
  have h_col_hash := hhash k
  -- Step 2: The digest verifies against the root
  have h_path_valid := hpath k
  -- Step 3: The tree leaf at the mapped position
  set j := (proof.openings k).colIdx
  have h_leaf := h_leaves j
  -- Step 4: The tree path verifies against the root
  have h_tree_path_valid := merkle_path_valid tree (leafIdx j)
  -- Step 5: The opening's auth path matches the tree's path
  have h_pm := h_path_match k
  -- Step 6: Both verify against the same root with the same path
  -- opening: verifyPath digest authPath = proof.root
  -- tree:    verifyPath (tree.getLeaf (leafIdx j)) (tree.getPath (leafIdx j)) = tree.root
  -- Since h_root : tree.root = proof.root and h_pm : authPath = tree.getPath (leafIdx j)
  -- By merkle_binding: digest = tree.getLeaf (leafIdx j) = hashColumn (tableau.column j)
  have h_digest_eq : (proof.openings k).digest =
      ColumnHash.hashColumn (tableau.column j) := by
    have h1 : verifyPath (proof.openings k).digest
        (tree.getPath (leafIdx j)) = proof.root := by
      rw [← h_pm]; exact h_path_valid
    have h2 : verifyPath (ColumnHash.hashColumn (tableau.column j))
        (tree.getPath (leafIdx j)) = proof.root := by
      rw [← h_leaf]; rw [← h_root]; exact h_tree_path_valid
    exact merkle_binding hcr_merkle _ _ _ (h1.trans h2.symm)
  -- Step 7: By column-hash injectivity
  -- h_col_hash : hashColumn colData = digest
  -- h_digest_eq : digest = hashColumn (tableau.column j)
  exact hcr_col (h_col_hash.trans h_digest_eq)

-- ============================================================
-- Section 5: Collision-extracting variant
-- ============================================================

open Classical in
/-- **Column opening authenticity (collision-extracting)**: same
    conclusion as `column_opening_authentic`, but instead of assuming
    collision resistance, concludes that either the opened data matches
    the committed tableau, OR a column-hash collision exists, OR a
    Merkle-hash collision exists. -/
theorem column_opening_authentic_or_collision
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (hverify : columnOpeningVerify proof)
    (tree : MerkleTree D d)
    (h_root : tree.root = proof.root)
    (leafIdx : Fin params.NCOL → Fin (2 ^ d))
    (tableau : Tableau F params)
    (h_leaves : ∀ j : Fin params.NCOL,
      tree.getLeaf (leafIdx j) =
        ColumnHash.hashColumn (tableau.column j))
    (h_path_match : ∀ k : Fin params.NREQ,
      (proof.openings k).authPath =
        tree.getPath (leafIdx ((proof.openings k).colIdx))) :
    (∀ k : Fin params.NREQ,
      (proof.openings k).colData =
        tableau.column (proof.openings k).colIdx) ∨
    ColumnHashCollision D F params.NROW ∨
    MerkleHashCollision D := by
  -- Try to apply the non-collision-extracting version
  by_cases hcr_merkle : Function.Injective
      (fun p : D × D => MerkleHash.hash2 p.1 p.2)
  · by_cases hcr_col : Function.Injective
        (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW))
    · left
      exact column_opening_authentic proof hcr_col hcr_merkle
        hverify tree h_root leafIdx tableau h_leaves h_path_match
    · right; left
      rw [injective_iff_no_collision] at hcr_col
      exact not_not.mp hcr_col
  · right; right
    rw [injective_iff_no_collision] at hcr_merkle
    exact not_not.mp hcr_merkle
