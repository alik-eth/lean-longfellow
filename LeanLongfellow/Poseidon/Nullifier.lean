import LeanLongfellow.Poseidon.Defs

/-! # Nullifier Correctness

A nullifier is `Poseidon(credential_id, contract_hash, salt)`.
It provides:
- **Binding**: same nullifier implies same `(credential, contract, salt)`
  (by collision resistance)
- **Contract scoping**: different `contract_hash` produces different nullifier
  (even with same credential and salt)
- **Replay detection**: same credential and contract with equal nullifier
  implies same salt
-/

variable {F : Type*}

-- ============================================================
-- Section 1: Nullifier computation
-- ============================================================

/-- Compute a nullifier: `Poseidon(credential_id, contract_hash, salt)`. -/
noncomputable def nullifier [PoseidonHash F 3]
    (credential_id contract_hash salt : F) : F :=
  poseidon3 credential_id contract_hash salt

-- ============================================================
-- Section 2: Determinism
-- ============================================================

/-- Nullifier determinism: same inputs always produce the same nullifier. -/
theorem nullifier_deterministic [PoseidonHash F 3]
    (cred contract salt : F) :
    nullifier cred contract salt = nullifier cred contract salt := rfl

-- ============================================================
-- Section 3: Binding
-- ============================================================

/-- Nullifier binding: same nullifier implies same inputs.
    Requires Poseidon collision resistance as an explicit hypothesis. -/
theorem nullifier_binding [PoseidonHash F 3]
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h : nullifier cred1 contract1 salt1 = nullifier cred2 contract2 salt2) :
    cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2 := by
  exact predicateCommitment_binding cred1 cred2 contract1 contract2 salt1 salt2 hcr h

-- ============================================================
-- Section 4: Contract scoping
-- ============================================================

/-- Contract scoping: different contracts produce different nullifiers
    (even with same credential and salt).
    Contrapositive of binding. -/
theorem nullifier_contract_scoped [PoseidonHash F 3]
    (cred contract1 contract2 salt : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h_diff : contract1 ≠ contract2) :
    nullifier cred contract1 salt ≠ nullifier cred contract2 salt := by
  intro h_eq
  have ⟨_, h_contract, _⟩ := nullifier_binding cred cred contract1 contract2 salt salt hcr h_eq
  exact h_diff h_contract

-- ============================================================
-- Section 5: Replay detection
-- ============================================================

/-- Replay prevention: same credential + same contract with equal nullifier
    implies same salt. The verifier stores seen nullifiers; a repeated
    nullifier means the same salt was reused. -/
theorem nullifier_replay_detection [PoseidonHash F 3]
    (cred contract salt1 salt2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h : nullifier cred contract salt1 = nullifier cred contract salt2) :
    salt1 = salt2 := by
  have ⟨_, _, h_salt⟩ := nullifier_binding cred cred contract contract salt1 salt2 hcr h
  exact h_salt
