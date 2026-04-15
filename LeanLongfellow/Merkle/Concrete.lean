import LeanLongfellow.Merkle.Defs
import LeanLongfellow.Poseidon.Concrete
import LeanLongfellow.Ligero.MerkleCommitment

/-! # Concrete Merkle and Column Hash from Poseidon Sponge

Instantiates `MerkleHash` and `ColumnHash` using `PoseidonSponge` as
the underlying hash primitive. Collision resistance appears as an
explicit hypothesis in the constructors, matching the sponge model.

## Main definitions

- `MerkleHash.ofPoseidon` -- binary Merkle hash from `PoseidonSponge F 2` + CR
- `ColumnHash.ofPoseidon` -- column hash from `PoseidonSponge F n` + CR

## Design note

`MerkleHash.hash2_injective` and `ColumnHash.hashColumn_injective` are
unconditional fields (no hypothesis parameter). To fill them we need an
actual injectivity proof, which we obtain from the CR hypothesis passed
to the constructor. The resulting instances are therefore `noncomputable`
(the hash function itself may be noncomputable) and carry the CR
assumption inside the instance -- the same pattern used by `PoseidonHash`.
-/

-- ============================================================
-- Section 1: MerkleHash from PoseidonSponge
-- ============================================================

variable {F : Type*} {NROW : ℕ}

/-- Helper: build the `Fin 2 -> F` input for the binary Poseidon hash. -/
private def mkPair (a b : F) : Fin 2 → F :=
  fun i => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b

/-- Construct a `MerkleHash` instance from a `PoseidonSponge` with
    arity 2 and an explicit collision-resistance hypothesis.

    `hash2 a b = PoseidonSponge.hash (mkPair a b)` -/
@[reducible]
noncomputable def MerkleHash.ofPoseidon [PoseidonSponge F 2]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 2))) :
    MerkleHash F where
  hash2 a b := PoseidonSponge.hash (mkPair a b)
  hash2_injective := by
    intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
    have h_input := hcr h
    have ha : a1 = a2 := congr_fun h_input ⟨0, by omega⟩
    have hb : b1 = b2 := congr_fun h_input ⟨1, by omega⟩
    exact Prod.ext ha hb

-- ============================================================
-- Section 2: ColumnHash from PoseidonSponge
-- ============================================================

/-- Construct a `ColumnHash` instance (with digest type `F`) from a
    `PoseidonSponge` with arity `NROW` and an explicit CR hypothesis.

    `hashColumn col = PoseidonSponge.hash col` -/
@[reducible]
noncomputable def ColumnHash.ofPoseidon [PoseidonSponge F NROW]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := NROW))) :
    ColumnHash F F NROW where
  hashColumn := PoseidonSponge.hash
  hashColumn_injective := hcr

-- ============================================================
-- Section 3: Consistency between MerkleHash and PoseidonHash
-- ============================================================

/-- When we already have a `PoseidonHash F 2` instance (which bundles CR),
    we get a `MerkleHash` directly. -/
@[reducible]
noncomputable def MerkleHash.ofPoseidonHash [PoseidonHash F 2] :
    MerkleHash F :=
  MerkleHash.ofPoseidon (PoseidonHash.injective (n := 2))

/-- When we already have a `PoseidonHash F NROW` instance,
    we get a `ColumnHash` directly. -/
@[reducible]
noncomputable def ColumnHash.ofPoseidonHash [PoseidonHash F NROW] :
    ColumnHash F F NROW :=
  ColumnHash.ofPoseidon (PoseidonHash.injective (n := NROW))
