# Fiat-Shamir Transform for Sumcheck: ROM Soundness

**Date:** 2026-04-14
**Status:** Approved
**Depends on:** Sumcheck formalization (M1–M5, complete)

## Motivation

The sumcheck protocol formalized in M1–M5 is interactive: the verifier sends random challenges. Longfellow's actual protocol is non-interactive — it uses the Fiat-Shamir transform, replacing verifier randomness with hash function outputs. The IETF draft (draft-google-cfrg-libzk) specifies this transform but has no mechanized security proof.

This design formalizes the Fiat-Shamir transform for our sumcheck protocol and proves it sound in the Random Oracle Model (ROM) with a concrete probability bound.

## Approach

Minimal probabilistic layer built from scratch. No VCVio dependency. Probability defined as counting over finite sets of oracle functions. Per-round oracle model (each round's randomness is an independent oracle call). Concrete bound, no asymptotics.

### Why not VCVio

VCVio provides a general-purpose probabilistic monad for cryptographic proofs in Lean 4. We chose not to depend on it because:
- VCVio is pinned to Lean 4.28.0 / Mathlib v4.28.0; we use Lean 4.30.0-rc1 / Mathlib master
- VCVio's Fiat-Shamir module targets 3-move Sigma protocols, not n-round sumcheck
- We only need narrow probabilistic reasoning (counting over finite oracle sets), not a full monad
- No version conflicts, no coupling to an external project's API stability

Migration to VCVio is possible later if the project grows to need general game-based proofs.

## File Structure

```
LeanLongfellow/
├── FiatShamir/
│   ├── Oracle.lean        # Random oracle type, probability over oracles
│   ├── Transform.lean     # Non-interactive prover/verifier
│   └── Soundness.lean     # ROM soundness theorem
```

## Component 1: Random Oracle Foundation (Oracle.lean)

### Types

```lean
/-- A random oracle for the sumcheck Fiat-Shamir transform.
    At round i, given the prover's polynomial, returns a field element. -/
def SumcheckOracle (F : Type*) (n : ℕ) := Fin n → Polynomial F → F

/-- The probability that a predicate holds over uniformly random oracle choices.
    |{H ∈ allOracles | P(H)}| / |allOracles|. -/
noncomputable def oracleProb (P : SumcheckOracle F n → Prop) [DecidablePred P] : ℚ :=
  (Finset.univ.filter P).card / Fintype.card (SumcheckOracle F n)
```

### Theorems

| Theorem | Statement |
|---------|-----------|
| `oracleProb_le_one` | `oracleProb P ≤ 1` |
| `oracleProb_mono` | If `P → Q` then `oracleProb P ≤ oracleProb Q` |
| `uniform_hit_prob` | For fixed `g : F[X]` and `v : F`, `Pr_H[H i g = v] = 1/|F|` |
| `uniform_root_prob` | For fixed nonzero `d : F[X]` with `deg ≤ 1`, `Pr_H[d.eval (H i g) = 0] ≤ 1/|F|` |
| `oracle_union_bound` | `Pr_H[∃ i, Pᵢ(H)] ≤ ∑ᵢ Pr_H[Pᵢ(H)]` |

`uniform_hit_prob` is the key new result: a uniformly random oracle output equals any fixed value with probability exactly `1/|F|`. This follows from the uniform distribution over `F`.

`uniform_root_prob` combines `uniform_hit_prob` with `roots_le_one_of_deg_le_one`.

## Component 2: Non-Interactive Protocol (Transform.lean)

### Types

```lean
/-- A non-interactive sumcheck proof: the n round polynomials. -/
structure FiatShamirProof (F : Type*) [Field F] (n : ℕ) where
  round_polys : Fin n → Polynomial F

/-- Derive challenges from an oracle and a proof. -/
def deriveChallenges (H : SumcheckOracle F n) (proof : FiatShamirProof F n) : Fin n → F :=
  fun i => H i (proof.round_polys i)

/-- Reconstruct interactive rounds from a non-interactive proof + oracle. -/
def toRounds (H : SumcheckOracle F n) (proof : FiatShamirProof F n) :
    Fin n → SumcheckRound F :=
  fun i => ⟨proof.round_polys i, deriveChallenges H proof i⟩

/-- Non-interactive verifier: derive challenges, run interactive verifier. -/
def fsVerifierAccepts (p : MultilinearPoly F n) (claimed_sum : F)
    (H : SumcheckOracle F n) (proof : FiatShamirProof F n) : Prop :=
  verifierAccepts p claimed_sum (toRounds H proof)
```

### Honest prover

The honest non-interactive prover computes round polynomials sequentially: round 0's polynomial is `sumFirstVar(p)`, the challenge `r₀ = H(0, g₀)` is derived, then round 1 operates on `partialEvalFirst(p, r₀)`, and so on.

This is defined recursively, matching the structure of `honestProver`:

```lean
noncomputable def fsHonestProver (p : MultilinearPoly F n) (H : SumcheckOracle F n) :
    FiatShamirProof F n
```

### Theorems

| Theorem | Statement |
|---------|-----------|
| `fsVerifier_iff` | `fsVerifierAccepts p c H proof ↔ verifierAccepts p c (toRounds H proof)` |
| `fsHonest_accepted` | The honest FS prover is always accepted (completeness) |

`fsHonest_accepted` follows directly from `sumcheck_completeness` since the honest FS prover produces exactly the honest interactive prover's polynomials with oracle-derived challenges.

## Component 3: ROM Soundness (Soundness.lean)

### Main theorem

```lean
theorem fiatShamir_soundness
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b, p.table b)
    (adversary : SumcheckOracle F n → FiatShamirProof F n)
    (hdeg : ∀ H i, (adversary H).round_polys i |>.natDegree ≤ 1) :
    oracleProb (fun H => fsVerifierAccepts p claimed_sum H (adversary H))
    ≤ n / Fintype.card F
```

### Adversary model

The adversary is a deterministic function `SumcheckOracle F n → FiatShamirProof F n`. Given oracle access, it produces a proof. The degree-≤-1 constraint on round polynomials is required (matching the interactive soundness statement). The probability is over the uniform choice of oracle.

This model captures any adversary that:
- Can query the oracle at any inputs during proof construction
- Produces round polynomials of degree ≤ 1
- Cannot predict oracle outputs on unqueried inputs (by the ROM assumption)

The bound `n/|F|` comes from: the adversary needs at least one oracle output (a challenge) to be a root of a nonzero degree-≤-1 polynomial. Each such event has probability ≤ 1/|F|. Union bound over n rounds.

### Proof structure

1. If `fsVerifierAccepts` holds, then `verifierAccepts p claimed_sum (toRounds H proof)` holds (by definition)
2. By `sumcheck_soundness_det` (with `hn`, `hclaim`), there exists round `i` and nonzero `diff` with `deg ≤ 1` such that `diff.eval (H i (proof.round_polys i)) = 0`
3. For fixed `proof.round_polys i` and fixed `diff`, the set of oracles H where `diff.eval (H i (proof.round_polys i)) = 0` has density ≤ 1/|F| (by `uniform_root_prob`)
4. Union bound over the n rounds: total probability ≤ n/|F|

Step 2→3 requires care: `proof` depends on `H` (the adversary is adaptive). The key insight is that even though the adversary chooses `proof.round_polys i` based on H, the value `H i (proof.round_polys i)` is still uniform over F conditioned on the adversary's view, because each oracle cell is independent. This is the standard ROM argument.

In the formalization, this is handled by fixing the adversary's choice of polynomial at round i and showing that the oracle's output on that input is still uniformly distributed (since the oracle is a uniformly random function).

### Helper lemma

```lean
/-- For any function f : SumcheckOracle F n → Fin n that selects a round,
    and any nonzero polynomial d of degree ≤ 1,
    the probability that H (f H) (g H) evaluates d to 0 is ≤ 1/|F|.
    This handles the adversary's adaptive choice. -/
theorem adaptive_root_prob ...
```

This is the technical heart. It requires showing that even when the adversary adaptively chooses which round to "attack" based on the oracle, the probability is still bounded. The proof uses the fact that the oracle values at different inputs are independent.

## Dependencies

### From existing codebase (no changes needed)
- `verifierAccepts` — interactive verifier predicate
- `honestProver` — interactive honest prover
- `sumcheck_completeness` — interactive completeness
- `sumcheck_soundness_det` — interactive soundness (deterministic form)
- `roots_le_one_of_deg_le_one` — Schwartz-Zippel for degree ≤ 1
- `sumFirstVar_natDegree_le` — honest round polys have degree ≤ 1

### From Mathlib
- `Fintype`, `Finset.card` — counting
- `Rat` (ℚ) — probability values

## Non-Goals

- Adaptive query tracking (counting adversary's oracle queries beyond the n protocol rounds)
- Asymptotic / negligible-function formulation
- Concrete hash function instantiation (SHA-256, SHAKE, etc.)
- Fiat-Shamir for protocols other than sumcheck
- Zero-knowledge preservation under Fiat-Shamir

## References

- Bellare-Rogaway, "Random oracles are practical" (CCS 1993)
- Bernhard-Pereira-Warinschi, "How not to prove yourself" (ASIACRYPT 2012)
- IETF draft-google-cfrg-libzk-01, Section 5 (non-interactive protocol)
- VCVio: https://github.com/dtumad/VCV-io (design reference, not a dependency)
