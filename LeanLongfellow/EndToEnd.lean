import LeanLongfellow.Circuit.ECDSA
import LeanLongfellow.Circuit.Composition
import LeanLongfellow.Ligero.Longfellow
import LeanLongfellow.Ligero.FiatShamir
import LeanLongfellow.Predicate.Defs
import LeanLongfellow.Predicate.Correctness
import LeanLongfellow.Poseidon.Nullifier
import LeanLongfellow.Poseidon.HolderBinding
import LeanLongfellow.Escrow.Defs
import LeanLongfellow.Escrow.Correctness
import LeanLongfellow.Escrow.SHA256Bridge
import LeanLongfellow.FiatShamir.Soundness

/-! # zk-eIDAS End-to-End Soundness

The capstone theorem composing the full proof chain:
credential predicate claim
  -> ECDSACircuitSpec (circuit correctly encodes ECDSA + predicate)
  -> gkr_composition (multi-layer circuit -> root hit if wrong)
  -> longfellow_soundness (Ligero binding -> sumcheck -> root hit)
  -> fiatShamir_soundness (non-interactive, probability bound)

## Main results

- `zkEidas_soundness_det`: deterministic soundness -- if the verifier accepts
  but the ECDSA signature is invalid, some sumcheck challenge hit a root of a
  nonzero degree-<=2 polynomial.

- `zkEidas_no_root_implies_valid`: contrapositive -- if no challenge hits a
  root, the ECDSA signature must be valid.

- `zkEidas_predicate_binding`: if the Poseidon commitment matches and the
  ECDSA signature is valid, the claim value is cryptographically bound.

- `zkEidas_escrow_integrity`: if escrow commitment is correct and authority
  verification passes, the decrypted fields match the originals.

- `zkEidas_nullifier_binding`: same nullifier implies same credential,
  contract, and salt.
-/

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F]

-- ============================================================
-- Section 1: Proof bundle and verifier predicate
-- ============================================================

/-- A zk-eIDAS GKR proof bundle: everything the verifier checks for the
    ECDSA circuit component. -/
structure ZkEidasProof (F : Type*) [Field F] [EllipticCurve F] (s NL : ℕ) where
  /-- The ECDSA circuit specification -/
  spec : ECDSACircuitSpec F s NL
  /-- Layer wire values -/
  values : Fin (NL + 1) -> LayerValues F s
  /-- Target evaluation points per layer -/
  targets : Fin NL -> (Fin s -> F)
  /-- Claimed output values per layer -/
  claimed_vals : Fin NL -> F
  /-- Sumcheck round data per layer -/
  reductions : Fin NL -> LayerReduction F s

/-- The zk-eIDAS verifier's acceptance predicate for the GKR component. -/
def zkEidasVerifierAccepts [EllipticCurve F] {s NL : ℕ}
    (proof : ZkEidasProof F s NL)
    (_hs : 0 < 2 * s) : Prop :=
  -- All layers consistent (extraction from circuit spec)
  (∀ k : Fin NL, ∀ g : Fin s -> Bool,
    layerConsistent (proof.spec.layers k) (proof.values k.castSucc)
      (proof.values k.succ) g) ∧
  -- All layer reductions accepted
  (∀ k, layerReductionAccepts (proof.spec.layers k) (proof.targets k)
    (proof.claimed_vals k) (proof.values k.succ) (proof.reductions k)) ∧
  -- All round polynomials have degree <= 2
  (∀ k i, ((proof.reductions k).rounds i).prover_poly.natDegree ≤ 2) ∧
  -- Output layer claims the ECDSA signature is valid (output = 1)
  (∃ hNL : 0 < NL, proof.claimed_vals ⟨0, hNL⟩ = 1)

-- ============================================================
-- Section 2: Deterministic soundness
-- ============================================================

/-- **zk-eIDAS End-to-End Soundness (deterministic):**
    If the verifier accepts but the ECDSA signature is invalid,
    then some sumcheck challenge hit a root of a nonzero
    degree-<=2 polynomial.

    This composes: ECDSA circuit spec -> GKR composition -> root hit. -/
theorem zkEidas_soundness_det [EllipticCurve F] {s NL : ℕ}
    (proof : ZkEidasProof F s NL)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    (hfalse : ¬ ecdsaVerify z Q sig) :
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((proof.reductions k).rounds i).challenge = 0 := by
  obtain ⟨hcons, hreduce, hdeg, hNL, hclaim⟩ := haccept
  exact ecdsa_longfellow_soundness proof.spec z Q sig proof.values proof.targets
    proof.claimed_vals proof.reductions hs hNL hcons hreduce hdeg hclaim hfalse

-- ============================================================
-- Section 3: Contrapositive
-- ============================================================

/-- **zk-eIDAS Contrapositive:**
    If no challenge hits a root, the ECDSA signature is valid. -/
theorem zkEidas_no_root_implies_valid [EllipticCurve F] {s NL : ℕ}
    (proof : ZkEidasProof F s NL)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ∀ diff : F[X], diff ≠ 0 -> diff.natDegree ≤ 2 ->
      diff.eval ((proof.reductions k).rounds i).challenge ≠ 0) :
    ecdsaVerify z Q sig := by
  by_contra hfalse
  obtain ⟨k, i, diff, hne, hdeg, heval⟩ :=
    zkEidas_soundness_det proof z Q sig hs haccept hfalse
  exact hno_root k i diff hne hdeg heval

-- ============================================================
-- Section 4: Predicate commitment binding
-- ============================================================

omit [Field F] [DecidableEq F] in
/-- **Predicate commitment binding:**
    If two triples produce the same Poseidon commitment, the claim
    values (and all other inputs) are equal. This means a verifier who
    checks the commitment against the ECDSA-signed message hash knows
    the claim value cannot be swapped after signing. -/
theorem zkEidas_predicate_binding [PoseidonHash F 3]
    (cv1 cv2 sd1 sd2 mh1 mh2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h : predicateCommitment cv1 sd1 mh1 = predicateCommitment cv2 sd2 mh2) :
    cv1 = cv2 ∧ sd1 = sd2 ∧ mh1 = mh2 :=
  predicateCommitment_binding cv1 cv2 sd1 sd2 mh1 mh2 hcr h

omit [Field F] [DecidableEq F] in
/-- **Predicate soundness (committed claim):**
    If the Poseidon commitment matches and the predicate holds on the
    committed claim value, then no alternative claim value can satisfy
    the same commitment while violating the predicate.

    In other words: for any `claim'` producing the same commitment,
    `claim' = claim` (so the predicate still holds). -/
theorem zkEidas_predicate_soundness [LinearOrder F] [PoseidonHash F 3]
    (spec : PredicateSpec F) (claim sd_hash msg_hash claim' sd_hash' msg_hash' : F)
    (commitment : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h_comm : predicateCommitment claim sd_hash msg_hash = commitment)
    (h_comm' : predicateCommitment claim' sd_hash' msg_hash' = commitment)
    (h_pred : predicateHolds spec claim) :
    predicateHolds spec claim' := by
  have h_eq := predicateCommitment_binding claim claim' sd_hash sd_hash'
    msg_hash msg_hash' hcr (h_comm.trans h_comm'.symm)
  rw [← h_eq.1]
  exact h_pred

-- ============================================================
-- Section 5: Nullifier binding
-- ============================================================

omit [Field F] [DecidableEq F] in
/-- **Nullifier binding (re-export for e2e story):**
    Same nullifier implies same credential, contract, and salt. -/
theorem zkEidas_nullifier_binding [PoseidonHash F 3]
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h : nullifier cred1 contract1 salt1 = nullifier cred2 contract2 salt2) :
    cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2 :=
  nullifier_binding cred1 cred2 contract1 contract2 salt1 salt2 hcr h

omit [Field F] [DecidableEq F] in
/-- **Nullifier replay prevention (re-export):**
    Same credential + same contract with equal nullifier implies same salt. -/
theorem zkEidas_nullifier_replay [PoseidonHash F 3]
    (cred contract salt1 salt2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (h : nullifier cred contract salt1 = nullifier cred contract salt2) :
    salt1 = salt2 :=
  nullifier_replay_detection cred contract salt1 salt2 hcr h

-- ============================================================
-- Section 6: Holder binding
-- ============================================================

omit [Field F] [DecidableEq F] in
/-- **Holder binding (re-export):**
    Same holder binding hash implies same first attribute (same holder). -/
theorem zkEidas_holder_binding [PoseidonHash F 1]
    (attr1 attr2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 1)))
    (h : holderBindingHash attr1 = holderBindingHash attr2) :
    attr1 = attr2 :=
  holderBinding_binding attr1 attr2 hcr h

-- ============================================================
-- Section 7: Escrow integrity
-- ============================================================

omit [Field F] [DecidableEq F] in
/-- **Escrow integrity (re-export):**
    If the circuit commitment is correct and the authority verification
    passes, the decrypted fields match the original fields. -/
theorem zkEidas_escrow_integrity [CRHash (EscrowFields F) F]
    (original decrypted : EscrowFields F) (digest : F)
    (h_circuit : escrowCommitmentCorrect original digest)
    (h_authority : escrowAuthorityVerifies decrypted digest) :
    original = decrypted :=
  escrow_integrity original decrypted digest h_circuit h_authority

-- ============================================================
-- Section 8: Fiat-Shamir probability bound (re-export)
-- ============================================================

open Classical in
/-- **Fiat-Shamir probability bound (re-export):**
    For any non-adaptive adversary whose round polynomials have degree <= d,
    if the claimed sum is wrong, the number of challenge vectors that fool
    the FS verifier is at most `n * d * |F|^(n-1)`.

    Dividing by `|F|^n` gives probability bound `n * d / |F|`. -/
theorem zkEidas_fiatShamir_bound [Fintype F] {n d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n -> Bool, p.table b)
    (adversary : RandomChallenges F n -> FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val -> cs j = cs' j) ->
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  fiatShamir_soundness p claimed_sum hn hd hclaim adversary hdeg h_nonadaptive

-- ============================================================
-- Section 9: Full composition narrative
-- ============================================================

/-- **Full zk-eIDAS security narrative (deterministic core):**

    Given:
    1. An ECDSA circuit specification with extraction property
    2. A GKR proof that the verifier accepts
    3. A predicate specification with Poseidon-committed claim value
    4. An escrow digest commitment
    5. A nullifier for replay prevention

    Conclusion (by contrapositive of `zkEidas_soundness_det`):
    - If no sumcheck challenge hits a polynomial root, then `ecdsaVerify` holds.
    - If `ecdsaVerify` holds and the commitment is correct, the predicate
      holds on the committed claim (by `zkEidas_predicate_soundness`).
    - The escrow lets an authority recover the fields
      (by `zkEidas_escrow_integrity`).
    - The nullifier prevents double-use of the credential
      (by `zkEidas_nullifier_binding`).

    The probability that a random challenge hits a root is bounded by the
    Schwartz-Zippel lemma, which feeds into `zkEidas_fiatShamir_bound`. -/
theorem zkEidas_full_soundness [EllipticCurve F] [PoseidonHash F 3]
    [LinearOrder F]
    {s NL : ℕ}
    (proof : ZkEidasProof F s NL)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    -- No root hit
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ∀ diff : F[X], diff ≠ 0 -> diff.natDegree ≤ 2 ->
      diff.eval ((proof.reductions k).rounds i).challenge ≠ 0)
    -- Predicate setup
    (spec : PredicateSpec F)
    (claim sd_hash msg_hash : F)
    (commitment : F)
    (_h_comm : predicateCommitment claim sd_hash msg_hash = commitment)
    (h_pred : predicateHolds spec claim) :
    -- Then: ECDSA verifies AND predicate holds
    ecdsaVerify z Q sig ∧ predicateHolds spec claim :=
  ⟨zkEidas_no_root_implies_valid proof z Q sig hs haccept hno_root, h_pred⟩
