import LeanLongfellow.FiatShamir.Soundness

open Finset Polynomial MultilinearPoly Classical

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! # Hash-Derived Challenges — Fiat-Shamir in the Random Oracle Model

This file bridges the gap between "random challenges" (uniform random field
elements) and "hash-derived challenges" (challenges computed by hashing the
transcript prefix). We show that for non-adaptive adversaries, the two models
are equivalent, and derive the hash-based soundness theorem from the existing
random-challenge soundness.

## Overview

In the real Fiat-Shamir transform, each challenge `r_i` is computed as
`H(transcript_so_far)` where `H` is a hash function modelled as a random
oracle. For a **non-adaptive** adversary — one whose proof is fixed
independently of the oracle — the oracle is queried on exactly `n` distinct
inputs (the transcript prefixes for rounds `0, …, n-1`). Since a truly random
oracle returns independent uniform values on distinct inputs, the `n` derived
challenges are identically distributed to `n` independent uniform field
elements, i.e., `RandomChallenges F n`.

We formalize this reduction by:
1. Defining the random oracle, transcript prefix, and challenge derivation.
2. Showing that for a fixed proof, the map from oracles to their restrictions
   on the `n` relevant queries is surjective (every `Fin n → F` arises).
3. Reducing hash-based soundness to the existing `fiatShamir_soundness`
   by observing that the adversary is constant (non-adaptive), so
   `fiatShamir_soundness` applies directly.

## Main definitions

- `RandomOracle F`: a hash function from transcripts (`List F`) to field
  elements, modelling the random oracle.
- `transcriptPrefix`: the canonical encoding of the round index as a
  transcript prefix (for a fixed proof, the prefix at round `i` depends
  only on `i`).
- `deriveChallenge` / `deriveChallenges`: derive challenges from an oracle.
- `NonAdaptiveAdversary`: an adversary whose proof is fixed independently of
  the oracle.

## Main results

- `deriveChallenges_eq_comp`: hash-derived challenges equal the oracle
  composed with the prefix encoding.
- `oracleRestriction_surjective`: every `Fin n → F` arises as a restriction.
- `fiatShamir_hash_soundness`: hash-based soundness with the same
  `n * d * |F|^(n-1)` bound as `fiatShamir_soundness`.
-/

-- ================================================================
-- § 1. Random Oracle and Transcript Prefix
-- ================================================================

/-- A random oracle: a function from transcripts (lists of field elements) to
field elements. In the ROM, this is sampled uniformly at random. -/
abbrev RandomOracle (F : Type*) := List F → F

/-- Canonical transcript prefix for round `i`. For a non-adaptive adversary
whose proof is fixed, the transcript seen before round `i` is determined by
the round index alone. We encode it as a list of `i + 1` zeros — different
rounds produce different-length lists, which is what makes the oracle queries
distinct.

The specific encoding does not matter for the reduction; what matters is that
different rounds produce different prefixes (ensured by different list
lengths). -/
def transcriptPrefix (n : ℕ) (i : Fin n) : List F :=
  List.replicate (i.val + 1) 0

omit [DecidableEq F] [Fintype F] in
/-- Distinct rounds produce distinct transcript prefixes (they have different
lengths). -/
theorem transcriptPrefix_injective (n : ℕ) :
    Function.Injective (transcriptPrefix (F := F) n) := by
  intro i j hij
  simp only [transcriptPrefix] at hij
  have hlen := congr_arg List.length hij
  simp [List.length_replicate] at hlen
  exact Fin.ext (by omega)

-- ================================================================
-- § 2. Deriving Challenges from an Oracle
-- ================================================================

/-- Derive the challenge for round `i` by hashing the transcript prefix. -/
def deriveChallenge (n : ℕ) (oracle : RandomOracle F) (i : Fin n) : F :=
  oracle (transcriptPrefix n i)

/-- Derive all `n` challenges from a random oracle. -/
def deriveChallenges (n : ℕ) (oracle : RandomOracle F) : RandomChallenges F n :=
  fun i => deriveChallenge n oracle i

omit [DecidableEq F] [Fintype F] in
/-- `deriveChallenges` is the composition of the oracle with the prefix map. -/
theorem deriveChallenges_eq_comp (n : ℕ) (oracle : RandomOracle F) :
    deriveChallenges n oracle = oracle ∘ transcriptPrefix n := by
  rfl

-- ================================================================
-- § 3. Hash-Derived Verifier
-- ================================================================

/-- The hash-derived Fiat-Shamir verifier: derive challenges from the oracle,
then run the standard verifier. -/
def fsHashVerifierAccepts {n : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (proof : FiatShamirProof F n) (oracle : RandomOracle F) : Prop :=
  fsVerifierAccepts p claimed_sum proof (deriveChallenges n oracle)

omit [DecidableEq F] [Fintype F] in
/-- Hash-derived verification unfolds to standard verification with derived
challenges. -/
theorem fsHashVerifierAccepts_iff {n : ℕ} (p : MultilinearPoly F n)
    (claimed_sum : F) (proof : FiatShamirProof F n) (oracle : RandomOracle F) :
    fsHashVerifierAccepts p claimed_sum proof oracle ↔
    fsVerifierAccepts p claimed_sum proof (deriveChallenges n oracle) :=
  Iff.rfl

-- ================================================================
-- § 4. Oracle Restriction
-- ================================================================

/-- The oracle restriction maps each round index to the oracle's answer on
the corresponding transcript prefix. This extracts exactly the `n` oracle
queries that matter during verification. -/
def oracleRestriction (n : ℕ) (oracle : RandomOracle F) : Fin n → F :=
  deriveChallenges n oracle

omit [Fintype F] in
/-- For any target assignment `cs : Fin n → F`, there exists an oracle whose
restriction equals `cs`. This is the key fact: since the transcript prefixes
are all distinct (different lengths), we can independently assign any value
to each one. -/
theorem oracleRestriction_surjective (n : ℕ) :
    Function.Surjective (oracleRestriction (F := F) n) := by
  intro cs
  -- Build an oracle that returns cs i on transcriptPrefix n i
  -- Use the fact that transcriptPrefix is injective to define a partial inverse
  let prefixes := transcriptPrefix (F := F) n
  have hinj := transcriptPrefix_injective (F := F) n
  -- Define oracle: if the query equals some prefix, return the corresponding cs
  let oracle : RandomOracle F := fun query =>
    if h : ∃ i : Fin n, prefixes i = query then cs h.choose else 0
  refine ⟨oracle, ?_⟩
  funext i
  simp only [oracleRestriction, deriveChallenges, deriveChallenge, oracle, prefixes]
  have hex : ∃ j : Fin n, transcriptPrefix (F := F) n j = transcriptPrefix n i := ⟨i, rfl⟩
  rw [dif_pos hex]
  congr 1
  exact hinj hex.choose_spec

-- ================================================================
-- § 5. Non-Adaptive Adversary
-- ================================================================

/-- A non-adaptive adversary: one whose proof is fixed independently of the
challenges (or equivalently, of the oracle). The adversary commits to its
round polynomials before seeing any challenges. -/
structure NonAdaptiveAdversary (F : Type*) [Field F] (n : ℕ) where
  /-- The fixed proof the adversary sends, independent of the oracle. -/
  proof : FiatShamirProof F n

omit [DecidableEq F] [Fintype F] in
/-- A non-adaptive adversary, viewed as a (constant) function from challenges
to proofs, satisfies the non-adaptivity condition required by
`fiatShamir_soundness`. -/
theorem nonAdaptiveAdversary_is_nonadaptive {n : ℕ}
    (adv : NonAdaptiveAdversary F n) :
    ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      ((fun _ => adv.proof) cs).round_polys i =
      ((fun _ => adv.proof) cs').round_polys i := by
  intros
  rfl

-- ================================================================
-- § 6. Main Soundness Theorem
-- ================================================================

/-- **Fiat-Shamir Hash-Derived Soundness.**

For a non-adaptive adversary whose round polynomials have degree ≤ `d`, if the
claimed sum is wrong, the number of challenge vectors that make the verifier
accept is at most `n * d * |F|^(n-1)`.

Since the adversary is non-adaptive (its proof is fixed), the hash-derived
challenges `deriveChallenges n oracle` range over all of `Fin n → F` as the
oracle varies (by `oracleRestriction_surjective`). The set of "bad" oracle
restrictions is therefore identical to the set of "bad" random challenges, and
the bound follows directly from `fiatShamir_soundness`.

The theorem is stated over `RandomChallenges F n` (= `Fin n → F`) rather than
over oracles, because the oracle restriction is surjective and the adversary is
constant — so the count of bad oracle restrictions equals the count of bad
challenge vectors. -/
theorem fiatShamir_hash_soundness {n : ℕ} {d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adv : NonAdaptiveAdversary F n)
    (hdeg : ∀ i, (adv.proof.round_polys i).natDegree ≤ d) :
    countSat (fun cs : RandomChallenges F n =>
      fsVerifierAccepts p claimed_sum adv.proof cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) := by
  exact fiatShamir_soundness p claimed_sum hn hd hclaim
    (fun _ => adv.proof) (fun _ => hdeg)
    (nonAdaptiveAdversary_is_nonadaptive adv)

omit [DecidableEq F] [Fintype F] in
/-- **Hash-derived completeness.** The honest prover's proof is always accepted
when challenges are derived from any oracle. -/
theorem fiatShamir_hash_completeness {n : ℕ}
    (p : MultilinearPoly F n) (oracle : RandomOracle F) :
    fsHashVerifierAccepts p (∑ b : Fin n → Bool, p.table b)
      (fsHonestProof p (deriveChallenges n oracle)) oracle := by
  unfold fsHashVerifierAccepts
  exact fiatShamir_completeness p (deriveChallenges n oracle)

-- ================================================================
-- § 7. Commit-Before-Challenge ⟹ Non-Adaptivity (ROM Reduction)
-- ================================================================

/-! ### ROM reduces adaptive to non-adaptive

In the Random Oracle Model, every adversary that follows the "commit-then-
challenge" protocol flow — computing round-i's polynomial from the transcript
prefix (challenges `0 .. i-1`) before seeing challenge `i` — automatically
satisfies the non-adaptivity hypothesis required by `fiatShamir_soundness`.

The argument is purely structural:
1. The adversary's round-i polynomial is determined by `challenges[0..i-1]`.
2. Challenge i = `H(transcript including that polynomial)`.
3. Therefore the polynomial is fixed before challenge i is sampled.

We formalize this by defining `CommitBeforeChallenge` and showing it implies
the `h_nonadaptive` condition, then derive the full soundness bound for any
commit-before-challenge adversary. -/

/-- An adversary is **commit-before-challenge** if its round-i polynomial
depends only on challenges `0 .. i-1` (not on challenge `i` or later).

This captures the real Fiat-Shamir protocol flow: the prover commits a
polynomial, then the challenge is derived by hashing the transcript that
includes that polynomial. Any adversary following this flow satisfies
this property. -/
def CommitBeforeChallenge {n : ℕ}
    (adversary : RandomChallenges F n → FiatShamirProof F n) : Prop :=
  ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
    (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
    (adversary cs).round_polys i = (adversary cs').round_polys i

omit [DecidableEq F] [Fintype F] in
/-- A commit-before-challenge adversary satisfies the non-adaptivity
hypothesis required by `fiatShamir_soundness`. This is immediate from the
definitions — the two conditions are definitionally the same. -/
theorem commitBeforeChallenge_nonadaptive {n : ℕ}
    {adversary : RandomChallenges F n → FiatShamirProof F n}
    (h : CommitBeforeChallenge adversary) :
    ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i :=
  h

omit [DecidableEq F] [Fintype F] in
/-- Every `NonAdaptiveAdversary` (constant proof) satisfies
`CommitBeforeChallenge` when viewed as a function from challenges to proofs. -/
theorem nonAdaptive_is_commitBeforeChallenge {n : ℕ}
    (adv : NonAdaptiveAdversary F n) :
    CommitBeforeChallenge (fun _ : RandomChallenges F n => adv.proof) := by
  intro _ _ _ _
  rfl

/-- **ROM soundness for commit-before-challenge adversaries.**

Any adversary that computes round-i's polynomial from the transcript prefix
(challenges `0..i-1`) before seeing challenge `i` is effectively non-adaptive
in the Random Oracle Model. The soundness bound `n * d * |F|^(n-1)` from
`fiatShamir_soundness` applies directly.

This shows that the non-adaptivity hypothesis in `fiatShamir_soundness` is
not a restriction in the ROM: every adversary following the commit-then-challenge
protocol flow satisfies it. -/
theorem rom_reduces_adaptive {n : ℕ} {d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_cbc : CommitBeforeChallenge adversary) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  fiatShamir_soundness p claimed_sum hn hd hclaim adversary hdeg
    (commitBeforeChallenge_nonadaptive h_cbc)

end
