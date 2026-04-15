import LeanLongfellow.Merkle.Defs
import LeanLongfellow.Poseidon.Concrete
import LeanLongfellow.Ligero.MerkleCommitment

/-! # Concrete Merkle and Column Hash from Poseidon Sponge

Instantiates `MerkleHash` and `ColumnHash` using `PoseidonSponge` as
the underlying hash primitive.

## Main definitions

- `MerkleHash.ofPoseidon` -- binary Merkle hash from `PoseidonSponge F 2`
- `ColumnHash.ofPoseidon` -- column hash from `PoseidonSponge F n`

## Design note

The `MerkleHash` and `ColumnHash` classes now only carry the hash
function, not an injectivity proof. Collision resistance is supplied
as an explicit hypothesis to theorems that need it. The constructors
below simply wire the Poseidon sponge into the class fields.
-/

-- ============================================================
-- Section 1: MerkleHash from PoseidonSponge
-- ============================================================

variable {F : Type*} {NROW : ℕ}

/-- Helper: build the `Fin 2 -> F` input for the binary Poseidon hash. -/
private def mkPair (a b : F) : Fin 2 → F :=
  fun i => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b

/-- Construct a `MerkleHash` instance from a `PoseidonSponge` with arity 2.

    `hash2 a b = PoseidonSponge.hash (mkPair a b)` -/
@[reducible]
noncomputable def MerkleHash.ofPoseidon [PoseidonSponge F 2] :
    MerkleHash F where
  hash2 a b := PoseidonSponge.hash (mkPair a b)

-- ============================================================
-- Section 2: ColumnHash from PoseidonSponge
-- ============================================================

/-- Construct a `ColumnHash` instance (with digest type `F`) from a
    `PoseidonSponge` with arity `NROW`.

    `hashColumn col = PoseidonSponge.hash col` -/
@[reducible]
noncomputable def ColumnHash.ofPoseidon [PoseidonSponge F NROW] :
    ColumnHash F F NROW where
  hashColumn := PoseidonSponge.hash

-- ============================================================
-- Section 3: Consistency between MerkleHash and PoseidonHash
-- ============================================================

/-- When we already have a `PoseidonHash F 2` instance,
    we get a `MerkleHash` directly. -/
@[reducible]
noncomputable def MerkleHash.ofPoseidonHash [PoseidonHash F 2] :
    MerkleHash F :=
  MerkleHash.ofPoseidon

/-- When we already have a `PoseidonHash F NROW` instance,
    we get a `ColumnHash` directly. -/
@[reducible]
noncomputable def ColumnHash.ofPoseidonHash [PoseidonHash F NROW] :
    ColumnHash F F NROW :=
  ColumnHash.ofPoseidon
