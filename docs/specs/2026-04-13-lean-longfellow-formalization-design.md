# Lean 4 Formal Verification of Longfellow Protocol Components

**Date:** 2026-04-13
**Status:** Approved
**Repo:** `lean-longfellow` (separate from zk-eidas)

## Motivation

Longfellow (Google's Sumcheck + Ligero proving system) has no mechanized formal verification. The IETF draft (draft-google-cfrg-libzk, Section 8) states mechanized soundness is a goal but not yet achieved. The system's security currently rests on paper proofs and three external audits.

This project formalizes Longfellow's core protocol components in Lean 4, producing:
- The first mechanized soundness proof for any Longfellow component
- A foundation for eIDAS trust service certification
- A publishable result useful for IETF standardization

## Approach: Mathlib Core + Custom MLE (Hybrid)

Use Mathlib for **field axioms and basic algebra** (`Field`, `Fintype`, `Finset`, `Polynomial`) but define multilinear polynomials with a **custom evaluation-based representation** that mirrors how Longfellow actually uses them — as functions `(Fin n → F) → F` with the multilinear extension property.

This avoids wrestling Mathlib's `MvPolynomial` into a multilinear shape while getting free theorems about fields.

### Why This Approach

The Isabelle AFP sumcheck proof (CSF 2024, Garvia Bosshard et al.) uses a similar strategy — abstract polynomial axioms with concrete instantiation later. We get the same modularity in Lean 4 while staying practical.

### Alternatives Considered

- **Mathlib-heavy (ArkLib style):** Maximum reuse but Mathlib's `MvPolynomial` doesn't naturally express multilinear evaluation tables. Build times ~15 min.
- **Minimal dependencies (risc0 style):** Full control but reproving basic algebra is tedious and error-prone. No ecosystem integration.

## Project Structure

```
lean-longfellow/
├── lakefile.lean          # Lake build config, Mathlib dependency
├── lean-toolchain         # Pin to stable Lean 4 + Mathlib version
├── LeanLongfellow/
│   ├── Field/
│   │   └── Basic.lean     # Field typeclass extensions if needed
│   ├── MLE/
│   │   ├── Defs.lean      # MultilinearPoly: (Fin n → F) → F
│   │   ├── Eval.lean      # Evaluation, partial evaluation, restriction
│   │   ├── Extension.lean # MLE uniqueness theorem
│   │   └── Props.lean     # Degree bounds, interpolation properties
│   ├── Sumcheck/
│   │   ├── Protocol.lean  # Prover/Verifier messages, transcript
│   │   ├── Completeness.lean
│   │   └── Soundness.lean # Schwartz-Zippel bound
│   └── GKR/               # Future: layered circuit reduction
│       └── ...
├── test/                  # #eval-based sanity checks
└── README.md
```

## Component 1: Multilinear Polynomial (MLE)

### Core Type

```lean
/-- A multilinear polynomial over `n` variables with coefficients in `F`.
    Represented as its evaluation table over {0,1}^n. -/
structure MultilinearPoly (F : Type*) [Field F] (n : ℕ) where
  /-- Evaluations at all points in {0,1}^n -/
  evals : (Fin n → F) → F
  /-- Additive: f(x with x_i = a+b) = f(x with x_i = a) + f(x with x_i = b) -/
  is_additive : ∀ (i : Fin n) (x : Fin n → F) (a b : F),
    evals (Function.update x i (a + b)) =
      evals (Function.update x i a) + evals (Function.update x i b)
  /-- Homogeneous: f(x with x_i = c*a) = c * f(x with x_i = a) -/
  is_homogeneous : ∀ (i : Fin n) (x : Fin n → F) (c a : F),
    evals (Function.update x i (c * a)) =
      c * evals (Function.update x i a)
```

### Definitions

| Definition | Description |
|-----------|-------------|
| `MultilinearPoly.ofEvals` | Construct MLE from evaluations on the Boolean hypercube `{0,1}^n` |
| `MultilinearPoly.eval` | Evaluate at any point in `F^n` (not just `{0,1}^n`) |
| `MultilinearPoly.partialEval` | Fix one variable, get an `(n-1)`-variate MLE |
| `MultilinearPoly.restrict` | Restrict to a hyperplane, yielding a univariate polynomial |

### Theorems

| Theorem | Statement |
|---------|-----------|
| `mle_unique` | If two multilinear polynomials agree on `{0,1}^n`, they agree everywhere |
| `mle_extension_exists` | Any function `{0,1}^n → F` has a unique multilinear extension |
| `mle_degree_bound` | Individual degree ≤ 1 in each variable |
| `mle_sum_hypercube` | `∑_{x ∈ {0,1}^n} p(x)` equals the sum of the evaluation table |
| `partial_eval_multilinear` | Partial evaluation preserves multilinearity in remaining variables |

`mle_unique` is the critical theorem — it's what makes sumcheck work. The verifier can check a claimed sum by reducing to point evaluations, and uniqueness guarantees the prover can't cheat.

## Component 2: Sumcheck Protocol

### Protocol Model

```lean
/-- A single round of the sumcheck protocol -/
structure SumcheckRound (F : Type*) [Field F] where
  /-- Prover sends a univariate polynomial of degree ≤ d -/
  prover_poly : Polynomial F
  /-- Verifier sends a random challenge -/
  challenge : F

/-- Full sumcheck protocol for claim: ∑_{x ∈ {0,1}^n} p(x) = c -/
structure SumcheckProtocol (F : Type*) [Field F] (n : ℕ) where
  /-- The multilinear polynomial being summed -/
  poly : MultilinearPoly F n
  /-- The claimed sum -/
  claimed_sum : F
  /-- The n rounds of interaction -/
  rounds : Fin n → SumcheckRound F
```

The verifier is modeled as deterministic (given its random challenges). The prover is modeled as arbitrary for soundness — we prove no cheating strategy works.

### Theorems

| Theorem | Statement |
|---------|-----------|
| `sumcheck_completeness` | Honest prover always convinces verifier. Error = 0. |
| `sumcheck_soundness` | For any cheating prover, if the claimed sum is wrong, the verifier rejects with probability ≥ `1 - n/|F|` (union bound over n rounds, Schwartz-Zippel with degree 1). |
| `sumcheck_round_reduce` | Each round reduces an n-variate sum claim to an (n-1)-variate sum claim via `partialEval`. |

### Schwartz-Zippel Dependency

A nonzero univariate polynomial of degree ≤ d has at most d roots. Mathlib provides this as `Polynomial.card_roots_le_degree` — used directly, not re-proved.

### Randomness Model

Challenges modeled as arbitrary elements of `F` chosen from a finite subset `S ⊆ F`. Soundness error is `n * d / |S|` where `d = 1` for multilinear. This matches the Isabelle formalization's approach and avoids needing a full probabilistic monad. VCVio-style probabilistic reasoning can be added later for Fiat-Shamir.

## Milestones

| # | Milestone | Deliverable |
|---|-----------|------------|
| M1 | Project scaffold | Lake project, Mathlib dep, lean-toolchain, CI |
| M2 | MLE formalization | `MultilinearPoly` type, `ofEvals`, `eval`, `partialEval`, `mle_unique`, `mle_extension_exists` |
| M3 | Sumcheck completeness | Protocol model, honest prover, completeness proof |
| M4 | Sumcheck soundness | Arbitrary prover, Schwartz-Zippel application, union bound |
| M5 | Field instantiation | Instantiate for a concrete prime field (proof-of-concept for Longfellow's F_p) |

Each milestone is independently useful and compiles on its own.

## Testing Strategy

`#eval` blocks that compute concrete MLE evaluations and sumcheck rounds over small examples (e.g., 2-3 variable polynomials over `ZMod 97`), confirming definitions are computationally correct before proving theorems about them.

## Non-Goals

- GKR reduction (future, builds on M4)
- Ligero commitment formalization (future)
- Fiat-Shamir transform (future, would integrate VCVio)
- SHA-256 circuit correctness (no tooling exists for C++ circuits)
- Zero-knowledge property (the Isabelle proof also doesn't cover this)
- Concrete Longfellow field instantiation with specific prime (M5 uses a generic prime as proof-of-concept)

## References

- Isabelle AFP Sumcheck: https://www.isa-afp.org/entries/Sumcheck_Protocol.html
- Garvia Bosshard et al., arXiv:2402.06093 (CSF 2024)
- ArkLib: https://github.com/Verified-zkEVM/ArkLib
- VCVio: https://github.com/dtumad/VCV-io (eprint 2024/1819)
- IETF draft: https://datatracker.ietf.org/doc/html/draft-google-cfrg-libzk-01
- Longfellow security analysis (Dec 2025): vendor/longfellow-zk/docs/static/reviews/
