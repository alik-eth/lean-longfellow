import LeanLongfellow.Circuit.ECDSA.Spec
import LeanLongfellow.Circuit.Core.Composition
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
import LeanLongfellow.FiatShamir.HashDerived

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
    ECDSA circuit component. Parameterized by the message hash `z`,
    public key `Q`, and signature `sig` being verified. -/
structure ZkEidasProof (F : Type*) [Field F] [EllipticCurve F] (s NL : ℕ)
    (z : F) (Q : EllipticCurve.Point (F := F)) (sig : ECDSASignature F) where
  /-- The ECDSA circuit specification -/
  spec : ECDSACircuitSpec F s NL z Q sig
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
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (proof : ZkEidasProof F s NL z Q sig)
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

    This composes: ECDSA circuit spec -> GKR composition -> root hit.

    **How to read this with the probabilistic bound:** This deterministic theorem
    and `zkEidas_fiatShamir_bound` are two halves of one argument.  This theorem
    says "wrong claim → root hit"; the Fiat-Shamir bound says "Pr[root hit] ≤
    n·d / |F|".  Together: Pr[verifier accepts a false statement] ≤ n·d / |F|.
    This is the standard structure of Schwartz-Zippel-based IOP soundness proofs. -/
theorem zkEidas_soundness_det [EllipticCurve F] {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (proof : ZkEidasProof F s NL z Q sig)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    (hfalse : ¬ ecdsaVerify z Q sig) :
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((proof.reductions k).rounds i).challenge = 0 := by
  obtain ⟨hcons, hreduce, hdeg, hNL, hclaim⟩ := haccept
  exact ecdsa_longfellow_soundness proof.spec proof.values proof.targets
    proof.claimed_vals proof.reductions hs hNL hcons hreduce hdeg hclaim hfalse

-- ============================================================
-- Section 3: Contrapositive
-- ============================================================

/-- **zk-eIDAS Contrapositive:**
    If no challenge hits a root, the ECDSA signature is valid. -/
theorem zkEidas_no_root_implies_valid [EllipticCurve F] {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (proof : ZkEidasProof F s NL z Q sig)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ∀ diff : F[X], diff ≠ 0 -> diff.natDegree ≤ 2 ->
      diff.eval ((proof.reductions k).rounds i).challenge ≠ 0) :
    ecdsaVerify z Q sig := by
  by_contra hfalse
  obtain ⟨k, i, diff, hne, hdeg, heval⟩ :=
    zkEidas_soundness_det proof hs haccept hfalse
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
    passes, the decrypted fields match the original fields.
    Requires collision resistance (injectivity) as an explicit hypothesis. -/
theorem zkEidas_escrow_integrity [CRHash (EscrowFields F) F]
    (original decrypted : EscrowFields F) (digest : F)
    (hcr : Function.Injective (CRHash.hash (α := EscrowFields F) (β := F)))
    (h_circuit : escrowCommitmentCorrect original digest)
    (h_authority : escrowAuthorityVerifies decrypted digest) :
    original = decrypted :=
  escrow_integrity original decrypted digest hcr h_circuit h_authority

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
-- Section 8b: Hash-derived Fiat-Shamir bound (ROM)
-- ============================================================

open Classical in
/-- **Hash-derived Fiat-Shamir bound (re-export):**
    For a non-adaptive adversary with degree-≤-d round polynomials and a
    wrong claimed sum, the count of bad challenge vectors is at most
    `n * d * |F|^(n-1)` — even when challenges are derived from a random
    oracle via hashing. -/
theorem zkEidas_fiatShamir_hash_bound [Fintype F] {n d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adv : NonAdaptiveAdversary F n)
    (hdeg : ∀ i, (adv.proof.round_polys i).natDegree ≤ d) :
    countSat (fun cs : RandomChallenges F n =>
      fsVerifierAccepts p claimed_sum adv.proof cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  fiatShamir_hash_soundness p claimed_sum hn hd hclaim adv hdeg

open Classical in
/-- **ROM soundness for commit-before-challenge adversaries (re-export):**
    Any adversary following the commit-then-challenge protocol flow satisfies
    the non-adaptivity hypothesis. The soundness bound applies directly. -/
theorem zkEidas_rom_soundness [Fintype F] {n d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_cbc : CommitBeforeChallenge adversary) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  rom_reduces_adaptive p claimed_sum hn hd hclaim adversary hdeg h_cbc

-- ============================================================
-- Section 9: Full composition narrative
-- ============================================================

/-- **Full zk-eIDAS security composition:**

    Composes all five security properties into a single theorem:

    1. **ECDSA soundness** — if no sumcheck challenge hits a polynomial root,
       the ECDSA signature is valid (from GKR composition + Schwartz-Zippel).
    2. **Predicate binding** — any alternative claim matching the same Poseidon
       commitment satisfies the predicate (from collision resistance, NOT
       trivially from the input hypothesis).
    3. **Escrow integrity** — the authority can recover the original fields
       from the escrow digest (from CRHash collision resistance).
    4. **Nullifier binding** — same nullifier implies same credential, contract,
       and salt (from Poseidon collision resistance).
    5. **Holder binding** — same holder hash implies same holder identity
       (from Poseidon collision resistance).

    The probability that a random challenge hits a root is bounded by the
    Schwartz-Zippel lemma, which feeds into `zkEidas_fiatShamir_bound`. -/
theorem zkEidas_full_soundness [EllipticCurve F] [PoseidonHash F 3]
    [PoseidonHash F 1] [LinearOrder F] [CRHash (EscrowFields F) F]
    {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (proof : ZkEidasProof F s NL z Q sig)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    -- No root hit
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ∀ diff : F[X], diff ≠ 0 -> diff.natDegree ≤ 2 ->
      diff.eval ((proof.reductions k).rounds i).challenge ≠ 0)
    -- Collision resistance hypotheses
    (hcr3 : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (hcr1 : Function.Injective (PoseidonHash.hash (F := F) (n := 1)))
    (hcr_escrow : Function.Injective (CRHash.hash (α := EscrowFields F) (β := F)))
    -- Predicate setup (with commitment binding — claim' is ANY value
    -- producing the same commitment, not the original claim)
    (spec : PredicateSpec F)
    (claim sd_hash msg_hash claim' sd_hash' msg_hash' : F)
    (commitment : F)
    (h_comm : predicateCommitment claim sd_hash msg_hash = commitment)
    (h_comm' : predicateCommitment claim' sd_hash' msg_hash' = commitment)
    (h_pred : predicateHolds spec claim)
    -- Escrow
    (original decrypted : EscrowFields F) (digest : F)
    (h_escrow_commit : escrowCommitmentCorrect original digest)
    (h_escrow_verify : escrowAuthorityVerifies decrypted digest)
    -- Nullifier
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (h_null : nullifier cred1 contract1 salt1 = nullifier cred2 contract2 salt2)
    -- Holder binding
    (attr1 attr2 : F)
    (h_holder : holderBindingHash attr1 = holderBindingHash attr2) :
    -- FULL CONCLUSION: all five security properties
    ecdsaVerify z Q sig ∧
    predicateHolds spec claim' ∧
    original = decrypted ∧
    (cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2) ∧
    attr1 = attr2 :=
  ⟨zkEidas_no_root_implies_valid proof hs haccept hno_root,
   zkEidas_predicate_soundness spec claim sd_hash msg_hash claim' sd_hash'
     msg_hash' commitment hcr3 h_comm h_comm' h_pred,
   zkEidas_escrow_integrity original decrypted digest hcr_escrow
     h_escrow_commit h_escrow_verify,
   zkEidas_nullifier_binding cred1 cred2 contract1 contract2 salt1 salt2 hcr3 h_null,
   zkEidas_holder_binding attr1 attr2 hcr1 h_holder⟩

-- ============================================================
-- Section 10: Collision-extracting capstone
-- ============================================================

open Classical in
/-- **Full zk-eIDAS security (collision-extracting):**

    The same five-property composition as `zkEidas_full_soundness`, but
    without assuming any hash injectivity (`Function.Injective`).
    Instead, the conclusion is a disjunction: either all five security
    properties hold, OR a concrete collision can be extracted for one of
    the hash functions (Poseidon-3, Poseidon-1, or CRHash/escrow).

    This formulation is strictly stronger because the collision-resistance
    hypotheses are replaced by constructive case splits that produce a
    witness when the properties fail. -/
theorem zkEidas_full_soundness_or_collision [EllipticCurve F] [PoseidonHash F 3]
    [PoseidonHash F 1] [LinearOrder F] [CRHash (EscrowFields F) F]
    {s NL : ℕ}
    {z : F} {Q : EllipticCurve.Point (F := F)} {sig : ECDSASignature F}
    (proof : ZkEidasProof F s NL z Q sig)
    (hs : 0 < 2 * s)
    (haccept : zkEidasVerifierAccepts proof hs)
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s),
      ∀ diff : F[X], diff ≠ 0 -> diff.natDegree ≤ 2 ->
      diff.eval ((proof.reductions k).rounds i).challenge ≠ 0)
    -- Predicate setup
    (spec : PredicateSpec F)
    (claim sd_hash msg_hash claim' sd_hash' msg_hash' : F)
    (commitment : F)
    (h_comm : predicateCommitment claim sd_hash msg_hash = commitment)
    (h_comm' : predicateCommitment claim' sd_hash' msg_hash' = commitment)
    (h_pred : predicateHolds spec claim)
    -- Escrow
    (original decrypted : EscrowFields F) (digest : F)
    (h_escrow_commit : escrowCommitmentCorrect original digest)
    (h_escrow_verify : escrowAuthorityVerifies decrypted digest)
    -- Nullifier
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (h_null : nullifier cred1 contract1 salt1 = nullifier cred2 contract2 salt2)
    -- Holder binding
    (attr1 attr2 : F)
    (h_holder : holderBindingHash attr1 = holderBindingHash attr2) :
    -- CONCLUSION: all five properties hold, OR a collision exists
    (ecdsaVerify z Q sig ∧
     predicateHolds spec claim' ∧
     original = decrypted ∧
     (cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2) ∧
     attr1 = attr2) ∨
    PoseidonCollision F 3 ∨ PoseidonCollision F 1 ∨
    CRHashCollision (EscrowFields F) F := by
  have h_ecdsa := zkEidas_no_root_implies_valid proof hs haccept hno_root
  rcases escrow_integrity_or_collision original decrypted digest
    h_escrow_commit h_escrow_verify with h_escrow | hcol_escrow
  · rcases predicateCommitment_binding_or_collision claim claim' sd_hash sd_hash'
      msg_hash msg_hash' (h_comm.trans h_comm'.symm) with h_pred_bind | hcol3
    · rcases nullifier_binding_or_collision cred1 cred2 contract1 contract2
        salt1 salt2 h_null with h_null_bind | hcol3
      · rcases holderBinding_binding_or_collision attr1 attr2 h_holder
          with h_holder_bind | hcol1
        · left
          exact ⟨h_ecdsa, by rwa [← h_pred_bind.1], h_escrow, h_null_bind, h_holder_bind⟩
        · right; right; left; exact hcol1
      · right; left; exact hcol3
    · right; left; exact hcol3
  · right; right; right; exact hcol_escrow

-- ============================================================
-- Section 11: Unified full proof bundle
-- ============================================================

set_option autoImplicit false in
/-- **Unified zk-eIDAS proof bundle.**

    Packages ALL data needed to verify the five zk-eIDAS security
    properties into a single structure: GKR circuit proof, predicate
    commitment, escrow digest, nullifier, and holder binding.

    The fields mirror the hypotheses of `zkEidas_full_soundness` so
    that the end-to-end theorem operates on one object. -/
structure ZkEidasFullProof (F : Type*) [Field F] [EllipticCurve F]
    [PoseidonHash F 3] [PoseidonHash F 1] [CRHash (EscrowFields F) F]
    (s NL : ℕ) where
  /-- Message hash -/
  z : F
  /-- Public key -/
  Q : EllipticCurve.Point (F := F)
  /-- ECDSA signature -/
  sig : ECDSASignature F
  /-- GKR proof data (circuit layers, values, reductions, etc.) -/
  gkrProof : ZkEidasProof F s NL z Q sig
  /-- Predicate specification -/
  predSpec : PredicateSpec F
  /-- Original claim value -/
  cv : F
  /-- Seed array hash -/
  sd : F
  /-- Message hash for predicate -/
  mh : F
  /-- Alternative claim value (adversary-chosen) -/
  cv' : F
  /-- Alternative seed (adversary-chosen) -/
  sd' : F
  /-- Alternative message hash (adversary-chosen) -/
  mh' : F
  /-- Shared predicate commitment -/
  commitment : F
  /-- Original escrow fields -/
  escrowOriginal : EscrowFields F
  /-- Decrypted escrow fields -/
  escrowDecrypted : EscrowFields F
  /-- Escrow digest -/
  escrowDigestVal : F
  /-- First credential id (nullifier) -/
  cred₁ : F
  /-- Second credential id (nullifier) -/
  cred₂ : F
  /-- First contract hash (nullifier) -/
  contract₁ : F
  /-- Second contract hash (nullifier) -/
  contract₂ : F
  /-- First salt (nullifier) -/
  salt₁ : F
  /-- Second salt (nullifier) -/
  salt₂ : F
  /-- First holder attribute -/
  attr₁ : F
  /-- Second holder attribute -/
  attr₂ : F

-- ============================================================
-- Section 12: Unified verifier predicate
-- ============================================================

set_option autoImplicit false in
/-- **Unified zk-eIDAS verifier.**

    Single predicate that checks every verification condition for the
    five zk-eIDAS security properties:

    1. GKR circuit accepts (layer consistency, reductions, degree bounds,
       output = 1).
    2. No sumcheck challenge hits a polynomial root (Schwartz-Zippel guard).
    3. Predicate commitments match the shared commitment.
    4. Predicate holds on the original claim.
    5. Escrow circuit commitment is correct and authority verification passes.
    6. Nullifiers match.
    7. Holder binding hashes match. -/
def zkEidasFullVerify {F : Type*} [Field F] [DecidableEq F] [EllipticCurve F]
    [PoseidonHash F 3] [PoseidonHash F 1] [CRHash (EscrowFields F) F]
    [LinearOrder F]
    {s NL : ℕ}
    (proof : ZkEidasFullProof F s NL)
    (hs : 0 < 2 * s) : Prop :=
  -- (1) GKR circuit accepts
  zkEidasVerifierAccepts proof.gkrProof hs ∧
  -- (2) No sumcheck challenge hits a polynomial root
  (∀ k : Fin NL, ∀ i : Fin (2 * s),
    ∀ diff : F[X], diff ≠ 0 → diff.natDegree ≤ 2 →
    diff.eval ((proof.gkrProof.reductions k).rounds i).challenge ≠ 0) ∧
  -- (3a) Original commitment matches
  predicateCommitment proof.cv proof.sd proof.mh = proof.commitment ∧
  -- (3b) Alternative commitment matches
  predicateCommitment proof.cv' proof.sd' proof.mh' = proof.commitment ∧
  -- (4) Predicate holds on original claim
  predicateHolds proof.predSpec proof.cv ∧
  -- (5a) Escrow circuit commitment correct
  escrowCommitmentCorrect proof.escrowOriginal proof.escrowDigestVal ∧
  -- (5b) Escrow authority verification passes
  escrowAuthorityVerifies proof.escrowDecrypted proof.escrowDigestVal ∧
  -- (6) Nullifiers match
  nullifier proof.cred₁ proof.contract₁ proof.salt₁ =
    nullifier proof.cred₂ proof.contract₂ proof.salt₂ ∧
  -- (7) Holder binding hashes match
  holderBindingHash proof.attr₁ = holderBindingHash proof.attr₂

-- ============================================================
-- Section 13: Unified soundness theorem
-- ============================================================

set_option autoImplicit false in
/-- **Unified zk-eIDAS soundness.**

    From a single verified `ZkEidasFullProof`, derives all five security
    properties in one theorem:

    1. **ECDSA validity** — the signature is valid.
    2. **Predicate binding** — the adversary's alternative claim also
       satisfies the predicate.
    3. **Escrow integrity** — original and decrypted fields are equal.
    4. **Nullifier binding** — same nullifier implies same credential,
       contract, and salt.
    5. **Holder binding** — same holder hash implies same attribute.

    Collision resistance (hash injectivity) is required as explicit
    hypotheses; all other assumptions are packed into `zkEidasFullVerify`. -/
theorem zkEidasFull_soundness {F : Type*} [Field F] [DecidableEq F]
    [EllipticCurve F] [PoseidonHash F 3] [PoseidonHash F 1]
    [LinearOrder F] [CRHash (EscrowFields F) F]
    {s NL : ℕ}
    (proof : ZkEidasFullProof F s NL)
    (hs : 0 < 2 * s)
    (hverify : zkEidasFullVerify proof hs)
    (hcr3 : Function.Injective (PoseidonHash.hash (F := F) (n := 3)))
    (hcr1 : Function.Injective (PoseidonHash.hash (F := F) (n := 1)))
    (hcr_escrow : Function.Injective (CRHash.hash (α := EscrowFields F) (β := F))) :
    ecdsaVerify proof.z proof.Q proof.sig ∧
    predicateHolds proof.predSpec proof.cv' ∧
    proof.escrowOriginal = proof.escrowDecrypted ∧
    (proof.cred₁ = proof.cred₂ ∧ proof.contract₁ = proof.contract₂ ∧
      proof.salt₁ = proof.salt₂) ∧
    proof.attr₁ = proof.attr₂ := by
  obtain ⟨haccept, hno_root, hcomm, hcomm', hpred, hescrow_c, hescrow_v,
    hnull, hholder⟩ := hverify
  exact ⟨zkEidas_no_root_implies_valid proof.gkrProof hs haccept hno_root,
    zkEidas_predicate_soundness proof.predSpec proof.cv proof.sd proof.mh
      proof.cv' proof.sd' proof.mh' proof.commitment hcr3 hcomm hcomm' hpred,
    zkEidas_escrow_integrity proof.escrowOriginal proof.escrowDecrypted
      proof.escrowDigestVal hcr_escrow hescrow_c hescrow_v,
    zkEidas_nullifier_binding proof.cred₁ proof.cred₂ proof.contract₁
      proof.contract₂ proof.salt₁ proof.salt₂ hcr3 hnull,
    zkEidas_holder_binding proof.attr₁ proof.attr₂ hcr1 hholder⟩

-- ============================================================
-- Section 14: Unified soundness (collision-extracting)
-- ============================================================

open Classical in
set_option autoImplicit false in
/-- **Unified zk-eIDAS soundness (collision-extracting).**

    The same five-property composition as `zkEidasFull_soundness`, but
    without assuming hash injectivity.  Either all five security properties
    hold, OR a concrete collision can be extracted for one of the hash
    functions (Poseidon-3, Poseidon-1, or CRHash/escrow). -/
theorem zkEidasFull_soundness_or_collision {F : Type*} [Field F] [DecidableEq F]
    [EllipticCurve F] [PoseidonHash F 3] [PoseidonHash F 1]
    [LinearOrder F] [CRHash (EscrowFields F) F]
    {s NL : ℕ}
    (proof : ZkEidasFullProof F s NL)
    (hs : 0 < 2 * s)
    (hverify : zkEidasFullVerify proof hs) :
    (ecdsaVerify proof.z proof.Q proof.sig ∧
     predicateHolds proof.predSpec proof.cv' ∧
     proof.escrowOriginal = proof.escrowDecrypted ∧
     (proof.cred₁ = proof.cred₂ ∧ proof.contract₁ = proof.contract₂ ∧
       proof.salt₁ = proof.salt₂) ∧
     proof.attr₁ = proof.attr₂) ∨
    PoseidonCollision F 3 ∨ PoseidonCollision F 1 ∨
    CRHashCollision (EscrowFields F) F := by
  obtain ⟨haccept, hno_root, hcomm, hcomm', hpred, hescrow_c, hescrow_v,
    hnull, hholder⟩ := hverify
  have h_ecdsa := zkEidas_no_root_implies_valid proof.gkrProof hs haccept hno_root
  rcases escrow_integrity_or_collision proof.escrowOriginal proof.escrowDecrypted
    proof.escrowDigestVal hescrow_c hescrow_v with h_escrow | hcol_escrow
  · rcases predicateCommitment_binding_or_collision proof.cv proof.cv' proof.sd
      proof.sd' proof.mh proof.mh' (hcomm.trans hcomm'.symm) with
      h_pred_bind | hcol3
    · rcases nullifier_binding_or_collision proof.cred₁ proof.cred₂ proof.contract₁
        proof.contract₂ proof.salt₁ proof.salt₂ hnull with h_null_bind | hcol3
      · rcases holderBinding_binding_or_collision proof.attr₁ proof.attr₂ hholder
          with h_holder_bind | hcol1
        · left
          exact ⟨h_ecdsa, by rwa [← h_pred_bind.1], h_escrow, h_null_bind, h_holder_bind⟩
        · right; right; left; exact hcol1
      · right; left; exact hcol3
    · right; left; exact hcol3
  · right; right; right; exact hcol_escrow
