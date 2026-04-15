import LeanLongfellow.Merkle.Defs
import LeanLongfellow.Merkle.Correctness
import LeanLongfellow.Ligero.Tableau

/-! # Merkle Tree Commitment for Ligero

Models Ligero's commitment as a Merkle root over tableau columns.
The prover commits by hashing tableau columns into a Merkle tree,
then opens requested columns with authentication paths.

## Key property

**Column opening binding**: if the prover commits to a Merkle root and
later opens a column with a valid authentication path, the opened column
is uniquely determined by the root and path. Two openings at the same
position with the same root and path must reveal the same column data.

This is `merkle_binding` (from `Merkle.Correctness`) lifted to the
Ligero setting via a collision-resistant column hash.

Each binding theorem has two variants:
- One taking `Function.Injective` as an explicit hypothesis.
- One concluding `result ∨ Collision` (collision-extracting).

## Design

We do NOT attempt to build a full `LigeroScheme` instance with Merkle
trees (that would require mapping column indices to `Fin (2^d)`,
handling the power-of-2 constraint, etc.). Instead we prove the
fundamental binding property that any concrete instantiation would rely on.
-/

-- ============================================================
-- Section 1: Column hash abstraction
-- ============================================================

/-- The column digest function: hash a column (vector of NROW field
    elements) into a single digest suitable as a Merkle leaf.

    In practice this might be Poseidon, SHA-256, etc. Collision
    resistance is modeled as an explicit hypothesis on theorems that
    need it, rather than a class field. -/
class ColumnHash (D : Type*) (F : Type*) (NROW : ℕ) where
  hashColumn : (Fin NROW → F) → D

-- ============================================================
-- Section 1b: Collision type
-- ============================================================

/-- A collision for a `ColumnHash` instance: two distinct column vectors
    with the same hash digest. -/
def ColumnHashCollision (D : Type*) (F : Type*) (NROW : ℕ)
    [ColumnHash D F NROW] : Prop :=
  HashCollision (ColumnHash.hashColumn (D := D) (F := F) (NROW := NROW))

-- ============================================================
-- Section 2: Tableau column extraction
-- ============================================================

/-- Extract column `j` from a tableau: the vector of all row values
    at column index `j`. -/
def Tableau.column {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params) (j : Fin params.NCOL) : Fin params.NROW → F :=
  fun i => T.rows i j

/-- Two tableaux are equal iff they agree on every column. -/
theorem Tableau.ext_column {F : Type*} [Field F] {params : LigeroParams}
    (T1 T2 : Tableau F params)
    (h : ∀ j : Fin params.NCOL, T1.column j = T2.column j) :
    T1 = T2 := by
  have : T1.rows = T2.rows := by
    funext i j
    have := congr_fun (h j) i
    exact this
  cases T1; cases T2; simp_all

-- ============================================================
-- Section 3: Merkle column opening
-- ============================================================

variable {D : Type*} [MerkleHash D]
variable {F : Type*} [Field F]

/-- A Merkle-committed column opening.

    Packages together all data needed to verify that a particular
    column was committed under a given Merkle root:
    - the root (commitment)
    - the column data
    - the column's digest (leaf of the Merkle tree)
    - an authentication path from the leaf to the root
    - proof that the path verifies -/
structure MerkleColumnOpening (D : Type*) [MerkleHash D]
    (F : Type*) (NROW : ℕ) (d : ℕ) where
  /-- The committed Merkle root -/
  root : D
  /-- The opened column data (NROW field elements) -/
  column : Fin NROW → F
  /-- The column's digest (Merkle leaf) -/
  digest : D
  /-- Authentication path from leaf to root -/
  path : AuthPath D d
  /-- The authentication path verifies against the root -/
  path_valid : verifyPath digest path = root

-- ============================================================
-- Section 4: Column opening binding (the key theorem)
-- ============================================================

omit [Field F] in
/-- **Column opening binding**: two openings with the same root and
    same authentication path must reveal the same column data.

    Requires collision resistance for both Merkle hash and column hash
    as explicit hypotheses.

    Proof sketch:
    1. By `merkle_binding`, same path + same reconstructed root
       implies same leaf digest.
    2. Both digests equal `hashColumn` of the respective columns.
    3. By `hashColumn_injective` (collision resistance), the columns
       are equal.

    This is the fundamental security guarantee: once the prover
    commits to a Merkle root, they cannot equivocate on any column
    opened via the same authentication path. -/
theorem column_opening_binding {NROW d : ℕ}
    [ColumnHash D F NROW]
    (hcr_merkle : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := NROW)))
    (op1 op2 : MerkleColumnOpening D F NROW d)
    (h_root : op1.root = op2.root)
    (h_path : op1.path = op2.path)
    (h_digest1 : op1.digest = ColumnHash.hashColumn op1.column)
    (h_digest2 : op2.digest = ColumnHash.hashColumn op2.column) :
    op1.column = op2.column := by
  -- Step 1: same path, same root => same digest
  have h_digest_eq : op1.digest = op2.digest :=
    merkle_binding_root hcr_merkle op1.root op1.digest op2.digest
      op1.path op2.path op1.path_valid (h_root ▸ op2.path_valid) h_path
  -- Step 2: same digest + injective hash => same column
  rw [h_digest1, h_digest2] at h_digest_eq
  exact hcr_col h_digest_eq

open Classical in
omit [Field F] in
/-- **Column opening binding (collision-extracting):**
    Same conclusion as `column_opening_binding`, OR a Merkle hash
    collision or column hash collision exists. -/
theorem column_opening_binding_or_collision {NROW d : ℕ}
    [ColumnHash D F NROW]
    (op1 op2 : MerkleColumnOpening D F NROW d)
    (h_root : op1.root = op2.root)
    (h_path : op1.path = op2.path)
    (h_digest1 : op1.digest = ColumnHash.hashColumn op1.column)
    (h_digest2 : op2.digest = ColumnHash.hashColumn op2.column) :
    op1.column = op2.column ∨
    MerkleHashCollision D ∨ ColumnHashCollision D F NROW := by
  -- Step 1: same path, same root => same digest OR merkle collision
  rcases merkle_binding_root_or_collision op1.root op1.digest op2.digest
      op1.path op2.path op1.path_valid (h_root ▸ op2.path_valid) h_path with
      h_digest_eq | hcol_merkle
  · -- Step 2: same digest => same column OR column hash collision
    rw [h_digest1, h_digest2] at h_digest_eq
    by_cases heq : op1.column = op2.column
    · left; exact heq
    · right; right; exact ⟨op1.column, op2.column, heq, h_digest_eq⟩
  · right; left; exact hcol_merkle

-- ============================================================
-- Section 5: Corollaries
-- ============================================================

omit [Field F] in
/-- Variant of binding using `merkle_binding_root` directly:
    if two column openings both verify against the same root
    using the same path, the columns agree.
    Requires collision resistance as explicit hypotheses. -/
theorem column_opening_binding' {NROW d : ℕ}
    [ColumnHash D F NROW]
    (hcr_merkle : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := NROW)))
    (root : D) (col1 col2 : Fin NROW → F)
    (path1 path2 : AuthPath D d)
    (h_v1 : verifyPath (ColumnHash.hashColumn col1) path1 = root)
    (h_v2 : verifyPath (ColumnHash.hashColumn col2) path2 = root)
    (h_same_path : path1 = path2) :
    col1 = col2 := by
  have h_digest := merkle_binding_root hcr_merkle root
    (ColumnHash.hashColumn col1)
    (ColumnHash.hashColumn col2)
    path1 path2 h_v1 h_v2 h_same_path
  exact hcr_col h_digest

omit [Field F] in
/-- If we extract a column from a tableau, hash it, put it in a
    Merkle tree, and extract the authentication path, then the
    opening is valid (the path verifies against the tree root).

    This connects the abstract `MerkleColumnOpening` to the concrete
    Merkle tree operations from `Merkle.Defs`. -/
theorem column_opening_from_tree {NROW d : ℕ}
    [ColumnHash D F NROW]
    (tree : MerkleTree D d) (j : Fin (2 ^ d))
    (col : Fin NROW → F)
    (h_leaf : tree.getLeaf j = ColumnHash.hashColumn col) :
    verifyPath (ColumnHash.hashColumn col) (tree.getPath j) = tree.root := by
  rw [← h_leaf]
  exact merkle_path_valid tree j

omit [Field F] in
/-- **No equivocation after commitment**: if the prover builds a
    Merkle tree, commits to its root, and later opens leaf `j` to
    two different columns (using the tree's own authentication path),
    those columns must be equal.

    Requires column hash collision resistance as an explicit hypothesis.

    This combines correctness (`merkle_path_valid`) with binding. -/
theorem no_equivocation_after_commit {NROW d : ℕ}
    [ColumnHash D F NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := NROW)))
    (tree : MerkleTree D d) (j : Fin (2 ^ d))
    (col1 col2 : Fin NROW → F)
    (h1 : tree.getLeaf j = ColumnHash.hashColumn col1)
    (h2 : tree.getLeaf j = ColumnHash.hashColumn col2) :
    col1 = col2 := by
  have : ColumnHash.hashColumn col1 = ColumnHash.hashColumn col2 :=
    h1.symm.trans h2
  exact hcr_col this

open Classical in
omit [Field F] in
/-- **No equivocation (collision-extracting):** same conclusion as
    `no_equivocation_after_commit`, OR a column hash collision. -/
theorem no_equivocation_after_commit_or_collision {NROW d : ℕ}
    [ColumnHash D F NROW]
    (tree : MerkleTree D d) (j : Fin (2 ^ d))
    (col1 col2 : Fin NROW → F)
    (h1 : tree.getLeaf j = ColumnHash.hashColumn col1)
    (h2 : tree.getLeaf j = ColumnHash.hashColumn col2) :
    col1 = col2 ∨ ColumnHashCollision D F NROW := by
  have heq : ColumnHash.hashColumn col1 = ColumnHash.hashColumn col2 :=
    h1.symm.trans h2
  by_cases hc : col1 = col2
  · left; exact hc
  · right; exact ⟨col1, col2, hc, heq⟩

-- ============================================================
-- Section 6: Tableau-level binding
-- ============================================================

/-- **Tableau column binding**: if two tableaux' columns hash to the
    same Merkle leaf at position `j`, then those columns are equal.

    Requires column hash collision resistance as an explicit hypothesis.

    This is the tableau-specific version of `no_equivocation_after_commit`. -/
theorem tableau_column_binding {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (tree : MerkleTree D d) (j : Fin (2 ^ d))
    (T1 T2 : Tableau F params)
    (jcol : Fin params.NCOL)
    (h1 : tree.getLeaf j = ColumnHash.hashColumn (T1.column jcol))
    (h2 : tree.getLeaf j = ColumnHash.hashColumn (T2.column jcol)) :
    T1.column jcol = T2.column jcol :=
  no_equivocation_after_commit hcr_col tree j (T1.column jcol) (T2.column jcol) h1 h2

omit [MerkleHash D] in
/-- If all columns of two tableaux hash to the same Merkle leaves,
    then the tableaux are equal.
    Requires column hash collision resistance as an explicit hypothesis. -/
theorem tableau_full_binding {params : LigeroParams}
    [ColumnHash D F params.NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (T1 T2 : Tableau F params)
    (h : ∀ j : Fin params.NCOL,
      ColumnHash.hashColumn (D := D) (T1.column j) =
      ColumnHash.hashColumn (T2.column j)) :
    T1 = T2 := by
  apply Tableau.ext_column
  intro j
  exact hcr_col (h j)

open Classical in
omit [MerkleHash D] in
/-- **Tableau full binding (collision-extracting):**
    Same conclusion as `tableau_full_binding`, OR a column hash collision. -/
theorem tableau_full_binding_or_collision {params : LigeroParams}
    [ColumnHash D F params.NROW]
    (T1 T2 : Tableau F params)
    (h : ∀ j : Fin params.NCOL,
      ColumnHash.hashColumn (D := D) (T1.column j) =
      ColumnHash.hashColumn (T2.column j)) :
    T1 = T2 ∨ ColumnHashCollision D F params.NROW := by
  by_cases hinj : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW))
  · left; exact tableau_full_binding hinj T1 T2 h
  · right
    rw [injective_iff_no_collision] at hinj
    exact not_not.mp hinj
