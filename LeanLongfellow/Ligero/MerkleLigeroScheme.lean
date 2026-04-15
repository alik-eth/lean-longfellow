import LeanLongfellow.Ligero.Concrete
import LeanLongfellow.Ligero.MerkleCommitment

/-! # Merkle-Committed Ligero Scheme

Provides a `LigeroScheme` instance where the commitment is a tuple of
column hashes (`Fin params.NCOL → D`) instead of the raw witness.

## Motivation

The `threeTestLigeroScheme` in `Concrete.lean` uses `commit := id`,
meaning the commitment IS the witness.  This is sound (binding holds)
but trivial: there is no hiding, and the prover can "commit" to a
different witness after the fact.  A real Ligero implementation commits
via a Merkle tree over hashed tableau columns.

This file bridges that gap.  The commitment is a column-hash tuple — the
data that would sit at the leaves of a Merkle tree in a full deployment.
The prover cannot change witness data after committing because
collision resistance of `ColumnHash.hashColumn` pins each column, and
`tableau_full_binding` lifts this to the entire tableau.

## Architecture

- **Commitment** = `Fin params.NCOL → D`, a tuple of column hashes.

- **commit** embeds the witness into a tableau via an injective function
  `embed`, then hashes each column.

- **verify** checks that the proof's inner witness embeds into a tableau
  whose column hashes match the commitment, AND that the three-test
  protocol accepts on that witness.

- **binding** composes hash injectivity + embedding injectivity + three-test
  soundness: matching column hashes → same tableau → same witness →
  three tests pass on `w` → `satisfiesAll w`.

## Design note

The scheme is parameterised by:

- `D` : digest type with `MerkleHash` and `ColumnHash` instances.
- `params` : Ligero parameters (NROW, NCOL, etc.).
- `embed` : an injective function mapping witnesses to tableaux.

The injectivity of `embed` is essential: it ensures that the commitment
uniquely determines the witness, not just the tableau.
-/

set_option autoImplicit false

open Finset

-- ============================================================
-- Section 1: Merkle-committed proof structure
-- ============================================================

variable {F : Type*} [Field F]
variable {D : Type*} [MerkleHash D]

/-- A Merkle Ligero proof carrying the prover's witness.

    In the real protocol the verifier never sees the full witness, only
    opened columns + authentication paths.  Here we model the logical
    content: the proof carries enough data (the witness and three-test
    evidence) for the verifier to check constraint satisfaction. -/
structure MerkleLigeroProof (F : Type*) [Field F]
    (params : LigeroParams) (m n q : ℕ) where
  /-- The three-test proof data (tableau, domain, LDT challenge) -/
  innerProof : LigeroProof F params m n q
  /-- The witness claimed by the prover -/
  witness : Fin n → F

-- ============================================================
-- Section 2: Merkle-committed verify predicate
-- ============================================================

/-- Merkle-committed Ligero verification.

    Two-phase check:

    1. **Commitment consistency**: every column of the tableau obtained
       by embedding the proof's witness hashes to the committed digest.
    2. **Three-test protocol**: LDT + linear + quadratic tests all pass
       on the proof's witness.

    Phase 1 prevents equivocation: the prover must present a witness
    whose embedded tableau matches the pre-committed column hashes. -/
def merkleVerify {params : LigeroParams} {m n q : ℕ}
    [ColumnHash D F params.NROW]
    (embed : (Fin n → F) → Tableau F params)
    (commitment : Fin params.NCOL → D)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : MerkleLigeroProof F params m n q) : Prop :=
  -- Phase 1: embedded witness tableau's columns hash to the commitment
  (∀ j : Fin params.NCOL,
    ColumnHash.hashColumn (D := D) ((embed proof.witness).column j) = commitment j) ∧
  -- Phase 2: three-test protocol accepts on the proof's witness
  threeTestVerify proof.witness lcs qcs proof.innerProof

-- ============================================================
-- Section 3: Binding — column hashes pin witness, three tests pin constraints
-- ============================================================

omit [MerkleHash D] in
/-- **Merkle-committed binding**: if `merkleVerify` accepts on
    `commit w`, the witness satisfies all constraints.

    Requires column hash collision resistance as an explicit hypothesis.

    Proof outline:
    1. Phase 1 gives: `∀ j, hashColumn (embed π.witness).column j
       = hashColumn (embed w).column j`.
    2. By `hashColumn_injective` on each column, the columns agree.
    3. By `Tableau.ext_column`, `embed π.witness = embed w`.
    4. By `embed_injective`, `π.witness = w`.
    5. Phase 2 gives: `threeTestVerify π.witness ...`.
    6. Substituting `π.witness = w`, we get `threeTestVerify w ...`.
    7. By `threeTest_binding`, `satisfiesAll w lcs qcs`. -/
theorem merkle_scheme_binding {params : LigeroParams} {m n q : ℕ}
    [ColumnHash D F params.NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (embed : (Fin n → F) → Tableau F params)
    (embed_injective : Function.Injective embed)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : MerkleLigeroProof F params m n q)
    (h : merkleVerify (D := D) embed
           (fun j => ColumnHash.hashColumn ((embed w).column j))
           lcs qcs proof) :
    satisfiesAll w lcs qcs := by
  obtain ⟨h_commit, h_three⟩ := h
  -- Step 1-2: column hashes agree → columns agree
  have h_cols : ∀ j : Fin params.NCOL,
      (embed proof.witness).column j = (embed w).column j := by
    intro j
    exact hcr_col (h_commit j)
  -- Step 3: columns agree → tableaux agree
  have h_tab : embed proof.witness = embed w :=
    Tableau.ext_column (embed proof.witness) (embed w) h_cols
  -- Step 4: embed injective → witnesses agree
  have h_wit : proof.witness = w :=
    embed_injective h_tab
  -- Steps 5-7: three-test binding on the original witness
  rw [h_wit] at h_three
  exact threeTest_binding w lcs qcs proof.innerProof h_three

open Classical in
omit [MerkleHash D] in
/-- **Merkle-committed binding (collision-extracting):**
    Same conclusion as `merkle_scheme_binding`, OR a column hash collision. -/
theorem merkle_scheme_binding_or_collision {params : LigeroParams} {m n q : ℕ}
    [ColumnHash D F params.NROW]
    (embed : (Fin n → F) → Tableau F params)
    (embed_injective : Function.Injective embed)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : MerkleLigeroProof F params m n q)
    (h : merkleVerify (D := D) embed
           (fun j => ColumnHash.hashColumn ((embed w).column j))
           lcs qcs proof) :
    satisfiesAll w lcs qcs ∨ ColumnHashCollision D F params.NROW := by
  by_cases hinj : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW))
  · left; exact merkle_scheme_binding hinj embed embed_injective w lcs qcs proof h
  · right
    rw [injective_iff_no_collision] at hinj
    exact not_not.mp hinj

-- ============================================================
-- Section 4: No equivocation — Merkle pins the tableau
-- ============================================================

omit [MerkleHash D] in
/-- **Merkle no-equivocation**: two proofs that both pass `merkleVerify`
    against the same commitment must carry the same witness.

    Requires column hash collision resistance as an explicit hypothesis.

    This is the property that `commit := id` trivially has but does not
    *enforce*: once the commitment is fixed, the witness is determined.
    Here it follows from hash injectivity + embedding injectivity. -/
theorem merkle_no_equivocation {params : LigeroParams} {m n q : ℕ}
    [ColumnHash D F params.NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (embed : (Fin n → F) → Tableau F params)
    (embed_injective : Function.Injective embed)
    (commitment : Fin params.NCOL → D)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof1 proof2 : MerkleLigeroProof F params m n q)
    (h1 : merkleVerify (D := D) embed commitment lcs qcs proof1)
    (h2 : merkleVerify (D := D) embed commitment lcs qcs proof2) :
    proof1.witness = proof2.witness := by
  have h_cols : ∀ j, (embed proof1.witness).column j =
      (embed proof2.witness).column j := by
    intro j
    exact hcr_col ((h1.1 j).trans (h2.1 j).symm)
  have h_tab := Tableau.ext_column _ _ h_cols
  exact embed_injective h_tab

-- ============================================================
-- Section 5: Completeness — honest prover's proof is accepted
-- ============================================================

omit [MerkleHash D] in
/-- **Merkle-committed completeness**: if the witness satisfies all
    constraints and the LDT passes, then `merkleVerify` accepts.

    The honest prover builds a proof carrying the true witness and
    a well-formed three-test proof. -/
theorem merkle_scheme_completeness {params : LigeroParams} {m n q : ℕ}
    [ColumnHash D F params.NROW]
    (embed : (Fin n → F) → Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (proof : MerkleLigeroProof F params m n q)
    (h_wit : proof.witness = w)
    (h_ldt : combinedRowIsCodeword proof.innerProof.domain
               proof.innerProof.tableau proof.innerProof.ldt_u)
    (h_sat : satisfiesAll w lcs qcs) :
    merkleVerify (D := D) embed
      (fun j => ColumnHash.hashColumn ((embed w).column j))
      lcs qcs proof := by
  constructor
  · intro j
    rw [h_wit]
  · rw [h_wit]
    exact threeTest_completeness w lcs qcs proof.innerProof h_ldt h_sat

-- ============================================================
-- Section 6: LigeroScheme instance
-- ============================================================

/-- **Merkle-committed Ligero scheme instance.**

    Strictly stronger than `threeTestLigeroScheme` because the commitment
    is a collision-resistant hash of the tableau columns, not the raw
    witness.  The prover cannot equivocate on any column after committing
    (`merkle_no_equivocation`).

    Requires column hash collision resistance as an explicit hypothesis.

    Parameters:
    - `D` — digest type (e.g., SHA-256 output, Poseidon hash)
    - `F` — field type
    - `params` — Ligero geometry (NROW, NCOL, BLOCK, NREQ)
    - `embed` — injective witness-to-tableau embedding
    - `embed_injective` — proof that `embed` is injective
    - `hcr_col` — collision resistance of column hash -/
@[reducible]
noncomputable def merkleLigeroScheme
    (D : Type) [MerkleHash D]
    (F : Type) [Field F]
    (params : LigeroParams) (n m q : ℕ)
    [ColumnHash D F params.NROW]
    (hcr_col : Function.Injective (ColumnHash.hashColumn (D := D) (F := F) (NROW := params.NROW)))
    (embed : (Fin n → F) → Tableau F params)
    (embed_injective : Function.Injective embed) :
    LigeroScheme F n m q where
  Commitment := Fin params.NCOL → D
  Proof := MerkleLigeroProof F params m n q
  commit := fun w => fun j => ColumnHash.hashColumn ((embed w).column j)
  verify := fun c lcs qcs proof =>
    merkleVerify (D := D) embed c lcs qcs proof
  binding := fun w lcs qcs proof h =>
    merkle_scheme_binding hcr_col embed embed_injective w lcs qcs proof h
