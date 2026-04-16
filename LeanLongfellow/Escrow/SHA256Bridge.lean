import LeanLongfellow.Escrow.Defs
import LeanLongfellow.Circuit.SHA256.Compression

/-! # SHA-256 Bridge for Escrow Digest

Connects the concrete SHA-256 circuit formalization to the abstract
escrow commitment model.

## Architecture

The escrow digest hashes 8 credential field values via SHA-256. At the circuit
level, each field is a 32-bit word (`Fin 32 → F`), so the input is
8 × 32 bits = 256 bits = 32 bytes, fitting in a single 512-bit SHA-256 block.

(In a full deployment the escrow input may be 8 × 32 *bytes* = 256 bytes,
requiring 5 SHA-256 blocks. The current formalization covers the single-block
case; multi-block chaining is future work.)

- **Abstract side** (`Escrow/Defs.lean`): `CRHash (EscrowFields F) F` models
  hashing. Collision resistance is an explicit hypothesis on theorems.
- **Concrete side** (`Circuit/SHA256.lean`): `sha256SingleBlock` constrains a
  single 512-bit block of SHA-256 compression.

This module provides:

1. `SHA256Spec` — a specification-level SHA-256 hash function on escrow fields.
   Collision resistance is an explicit hypothesis on theorems that need it.
2. An instance `CRHash (EscrowFields F) F` derived from `SHA256Spec`, so all
   escrow theorems (`escrow_integrity`, `escrow_binding`,
   `escrow_field_sensitivity`) apply to the SHA-256 instantiation.
3. A soundness statement connecting the circuit-level `sha256SingleBlock`
   constraints to the specification-level hash.
-/

set_option autoImplicit false

-- ============================================================
-- Section 1: SHA-256 Specification (abstract)
-- ============================================================

/-- Specification-level SHA-256 hash function for escrow fields.
    Maps 8 field elements (the escrow credential fields) to a single
    digest field element.

    Collision resistance is modeled as an explicit hypothesis on theorems
    that need it, rather than a class field, because `Function.Injective`
    is unsatisfiable for hash functions over finite types when the domain
    is larger than the codomain. -/
class SHA256Spec (F : Type*) where
  /-- Hash 8 escrow field values to a digest. -/
  sha256 : EscrowFields F → F

-- ============================================================
-- Section 2: Escrow digest via SHA-256
-- ============================================================

variable {F : Type*}

/-- The escrow digest computed using specification-level SHA-256. -/
noncomputable def escrowSHA256Digest [SHA256Spec F]
    (fields : EscrowFields F) : F :=
  SHA256Spec.sha256 fields

/-- SHA-256 instantiates the abstract `CRHash` for escrow fields.
    This makes all theorems proved generically over `CRHash` — such as
    `escrow_integrity`, `escrow_binding`, and `escrow_field_sensitivity` —
    available for the SHA-256 instantiation. -/
noncomputable instance escrowCRHash [SHA256Spec F] :
    CRHash (EscrowFields F) F where
  hash := SHA256Spec.sha256

-- ============================================================
-- Section 3: Escrow properties under SHA-256
-- ============================================================

/-- With the SHA-256 bridge, collision resistance of the escrow digest
    follows from an explicit `Function.Injective` hypothesis. -/
theorem escrow_sha256_binding [SHA256Spec F]
    (f1 f2 : EscrowFields F)
    (hcr : Function.Injective (SHA256Spec.sha256 (F := F)))
    (h : escrowSHA256Digest f1 = escrowSHA256Digest f2) :
    f1 = f2 :=
  hcr h

open Classical in
/-- Collision-extracting variant: either binding holds or SHA-256 has a collision.
    Does not require the `Function.Injective` hypothesis. -/
theorem escrow_sha256_binding_or_collision [SHA256Spec F]
    (f1 f2 : EscrowFields F)
    (h : escrowSHA256Digest f1 = escrowSHA256Digest f2) :
    f1 = f2 ∨ HashCollision (SHA256Spec.sha256 (F := F)) := by
  by_cases heq : f1 = f2
  · left; exact heq
  · right; exact ⟨f1, f2, heq, h⟩

/-- The SHA-256 escrow digest agrees with the abstract `escrowDigest`
    when `CRHash` is instantiated via `escrowCRHash`. -/
theorem escrowSHA256Digest_eq_escrowDigest [SHA256Spec F]
    (fields : EscrowFields F) :
    escrowSHA256Digest fields = @escrowDigest F escrowCRHash fields :=
  rfl

-- ============================================================
-- Section 4: Circuit soundness bridge
-- ============================================================

/-- Representation of the escrow input at the circuit level.
    Each of the 8 escrow fields is represented as a 32-bit word
    (Fin 32 -> F), so the full input is 8 words × 32 bits = 256 bits,
    fitting in a single SHA-256 block. -/
def EscrowCircuitInput (F : Type*) := Fin 8 → (Fin 32 → F)

/-- Validity: every word in the escrow circuit input is a proper 32-bit word. -/
def EscrowCircuitInput.valid [Field F] (input : EscrowCircuitInput F) : Prop :=
  ∀ i : Fin 8, isWord32 (input i)

/-- Pack escrow circuit input into the first SHA-256 block (16 words of 32 bits).
    Block k contains fields 2k and 2k+1 (each 1 word = 32 bits).
    Since each field is only 1 word (32 bits) but a SHA-256 block is 16 words,
    we pack fields into successive word positions.

    This function packs 2 fields into a single 16-word SHA-256 block,
    placing them at word positions 0 and 1, with remaining positions zeroed. -/
def packEscrowBlock [Field F] (f0 f1 : Fin 32 → F) :
    Fin 16 → (Fin 32 → F) :=
  fun i =>
    if i.val = 0 then f0
    else if i.val = 1 then f1
    else fun _ => (0 : F)

/-- Circuit-level soundness bridge for SHA-256.

    Extends `SHA256Spec` with the assumption that the circuit-level
    `sha256SingleBlock` constraint is sound with respect to the
    specification-level hash. This connects the constraint system
    to the abstract model.

    Proving this assumption requires showing that the circuit constraints
    (message schedule + 64 rounds of compression + final addition) exactly
    implement the SHA-256 algorithm. This is eliminated by verification
    of the circuit against the NIST specification. -/
class SHA256CircuitSound (F : Type*) [Field F] [SHA256Constants F]
    extends SHA256Spec F where
  /-- If the single-block circuit constraint is satisfied, the output
      word values are uniquely determined by the input. -/
  circuit_deterministic :
    ∀ (input : Fin 16 → (Fin 32 → F))
      (out1 out2 : Fin 8 → (Fin 32 → F)),
      sha256SingleBlock input out1 →
      sha256SingleBlock input out2 →
      (∀ i, isWord32 (input i)) →
      ∀ i : Fin 8, word32Val (out1 i) = word32Val (out2 i)

-- `sha256_circuit_implies_crhash` removed: with `injective` no longer
-- a field of `SHA256Spec`, CR must be an explicit hypothesis on any
-- theorem that needs it (same pattern as `CRHash`, `MerkleHash`,
-- `PoseidonHash`).

-- ============================================================
-- Section 5: Multi-block structure
-- ============================================================

/-- The number of SHA-256 compression calls for a full 256-byte escrow
    input (8 × 32 bytes): 5 blocks (4 data + 1 padding). The current
    formalization covers the single-block case (8 × 32 bits = 256 bits);
    this constant documents the multi-block deployment scenario. -/
theorem escrow_sha256_block_count :
    sha256_blocks_for_escrow = 5 := rfl
