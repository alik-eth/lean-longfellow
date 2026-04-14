import LeanLongfellow.Escrow.Defs

/-! # Escrow Digest Commitment — Correctness Properties

Proves the key security properties of the escrow commitment scheme:

1. **Integrity**: if the circuit commitment is correct and the authority
   verification passes, the decrypted fields equal the original fields.
2. **Binding**: the escrow digest uniquely determines the fields
   (collision resistance).
3. **Field sensitivity**: changing any single field changes the digest.
4. **Block count**: the SHA-256 block count for 256-byte input is 5.
-/

variable {F : Type*} [CRHash (EscrowFields F) F]

-- ============================================================
-- Section 1: Escrow integrity
-- ============================================================

/-- If the circuit commitment is correct and the authority verification
    passes, then the decrypted fields match the original fields.
    This is the key escrow integrity property. -/
theorem escrow_integrity
    (original decrypted : EscrowFields F) (digest : F)
    (h_circuit : escrowCommitmentCorrect original digest)
    (h_authority : escrowAuthorityVerifies decrypted digest) :
    original = decrypted := by
  unfold escrowCommitmentCorrect escrowAuthorityVerifies escrowDigest at *
  exact CRHash.collision_resistant (h_circuit.trans h_authority.symm)

-- ============================================================
-- Section 2: Binding
-- ============================================================

/-- The escrow digest uniquely determines the fields
    (by collision resistance). -/
theorem escrow_binding
    (f1 f2 : EscrowFields F)
    (h : escrowDigest f1 = escrowDigest f2) :
    f1 = f2 := by
  exact CRHash.collision_resistant h

-- ============================================================
-- Section 3: Field sensitivity
-- ============================================================

/-- Changing any single field changes the digest. -/
theorem escrow_field_sensitivity
    (fields : EscrowFields F) (i : Fin 8) (v : F)
    (h_diff : fields i ≠ v) :
    escrowDigest fields ≠ escrowDigest (Function.update fields i v) := by
  intro h_eq
  have heq := CRHash.collision_resistant h_eq
  have : fields i = v := by
    have := congr_fun heq i
    simp [Function.update] at this
    exact this
  exact h_diff this

-- ============================================================
-- Section 4: SHA-256 block count
-- ============================================================

/-- The number of SHA-256 blocks for a 256-byte input is
    ⌈(256 + 9) / 64⌉ = 5. -/
theorem sha256_blocks_correct : sha256_blocks_for_escrow = (256 + 9 + 63) / 64 := by
  native_decide
