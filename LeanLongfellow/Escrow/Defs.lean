import Mathlib.Logic.Function.Basic
import LeanLongfellow.Poseidon.Defs

/-! # Escrow Digest Commitment — Definitions

Formalizes the escrow digest commitment used in zk-eIDAS.
The escrow digest is a SHA-256 hash of 8 credential fields (each 32 bytes).
The circuit proves in zero knowledge that the digest matches the hash of the
fields, without revealing them.

We model SHA-256 abstractly as a hash function. Collision resistance is
modeled as an explicit hypothesis on theorems that need it, rather than a
class field, because `Function.Injective` is unsatisfiable for hash functions
over finite types when the domain is larger than the codomain.
-/

-- ============================================================
-- Section 1: Abstract collision-resistant hash
-- ============================================================

/-- Abstract hash function modelling SHA-256.
    Collision resistance is modeled as an explicit hypothesis on theorems
    that need it, rather than a class field, because `Function.Injective`
    is unsatisfiable for hash functions over finite types when the domain
    is larger than the codomain. -/
class CRHash (α β : Type*) where
  hash : α → β

-- ============================================================
-- Section 1b: Collision type
-- ============================================================

/-- A collision for a `CRHash` instance: two distinct inputs with the same hash. -/
def CRHashCollision (α β : Type*) [CRHash α β] : Prop :=
  HashCollision (CRHash.hash (α := α) (β := β))

-- ============================================================
-- Section 2: Escrow field types
-- ============================================================

/-- Escrow fields: 8 credential field values.
    In zk-eIDAS the input to the escrow hash is 8 × 32-byte fields. -/
def EscrowFields (F : Type*) := Fin 8 → F

-- ============================================================
-- Section 3: Digest and commitment predicates
-- ============================================================

variable {F : Type*}

/-- The escrow digest: hash of the 8 concatenated credential fields. -/
noncomputable def escrowDigest [CRHash (EscrowFields F) F]
    (fields : EscrowFields F) : F :=
  CRHash.hash fields

/-- The escrow commitment claim: the circuit asserts that
    the digest equals the hash of the witness fields. -/
def escrowCommitmentCorrect [CRHash (EscrowFields F) F]
    (fields : EscrowFields F) (claimed_digest : F) : Prop :=
  escrowDigest fields = claimed_digest

/-- Escrow verification by the authority after decryption:
    the authority re-hashes the decrypted fields and checks
    against the digest committed in the proof. -/
def escrowAuthorityVerifies [CRHash (EscrowFields F) F]
    (decrypted_fields : EscrowFields F) (circuit_digest : F) : Prop :=
  escrowDigest decrypted_fields = circuit_digest

-- ============================================================
-- Section 4: SHA-256 block count for 256-byte input
-- ============================================================

/-- The number of SHA-256 blocks for 256-byte input is 5.
    (4 data blocks of 64 bytes + 1 padding block) -/
def sha256_blocks_for_escrow : Nat := 5
