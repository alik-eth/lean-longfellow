# Abstract Ligero Interface + End-to-End Longfellow Soundness

**Date:** 2026-04-14
**Status:** Approved
**Depends on:** MLE (complete), Sumcheck (complete), Fiat-Shamir (complete)

## Motivation

Longfellow = Sumcheck (inner proof) + Ligero (outer proof). We've formalized the sumcheck half. The remaining gap is Ligero — the commitment scheme that proves the padded sumcheck transcript satisfies derived constraints without revealing the witness.

Rather than formalizing Ligero's internals (Reed-Solomon, Merkle trees, proximity testing), this spec defines Ligero as a **structured abstraction** with a binding axiom, then proves end-to-end Longfellow soundness by composition. The Ligero internals can be filled in later as a separate spec.

## Approach

Model Ligero as a typeclass with commit/verify operations and a binding property. Define the constraint types (linear + quadratic) that Longfellow generates from the padded sumcheck transcript. Prove that if Ligero binding holds, the Longfellow verifier never accepts a wrong claim.

### Key insight from the design phase

If Ligero's binding axiom holds (committed witness satisfies constraints → constraints were generated from a correct sumcheck), then the soundness error comes ENTIRELY from Ligero's probabilistic binding failure. The sumcheck's `n/|F|` error is subsumed — the constraints already encode sumcheck correctness. So:

- **Deterministic:** If Ligero binding holds, the verifier never accepts a wrong claim.
- **Probabilistic:** `Pr[accept wrong claim] ≤ ε_ligero`

This is stronger and cleaner than the initial `n/|F| + ε_ligero` estimate.

## File Structure

```
LeanLongfellow/
├── Ligero/
│   ├── Constraints.lean    # LinearConstraints, QuadConstraint, satisfiesLinear/Quad/All
│   ├── Interface.lean      # LigeroScheme typeclass (commit, verify, binding)
│   ├── Generate.lean       # Constraint generation from sumcheck transcript
│   └── Longfellow.lean     # longfellowVerifierAccepts, soundness theorems
```

## Component 1: Constraint Types (Constraints.lean)

### Types

```lean
/-- A system of linear constraints: A · w = b -/
structure LinearConstraints (F : Type*) [Field F] (m n : ℕ) where
  matrix : Fin m → Fin n → F
  target : Fin m → F

/-- A quadratic constraint: w[x] · w[y] = w[z] -/
structure QuadConstraint (n : ℕ) where
  left : Fin n
  right : Fin n
  output : Fin n
```

### Predicates

```lean
def satisfiesLinear (w : Fin n → F) (lc : LinearConstraints F m n) : Prop :=
  ∀ i, ∑ j, lc.matrix i j * w j = lc.target i

def satisfiesQuad (w : Fin n → F) (qc : QuadConstraint n) : Prop :=
  w qc.left * w qc.right = w qc.output

def satisfiesAll (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) : Prop :=
  satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i)
```

## Component 2: Abstract Ligero Interface (Interface.lean)

### Typeclass

```lean
class LigeroScheme (F : Type*) [Field F] (n m q : ℕ) where
  Commitment : Type
  Proof : Type
  commit : (Fin n → F) → Commitment
  verify : Commitment → LinearConstraints F m n →
           (Fin q → QuadConstraint n) → Proof → Prop
  /-- Binding: if verify accepts on a commitment to w, then w satisfies the constraints. -/
  binding : ∀ (w : Fin n → F) (lcs : LinearConstraints F m n)
              (qcs : Fin q → QuadConstraint n) (π : Proof),
    verify (commit w) lcs qcs π → satisfiesAll w lcs qcs
```

The `binding` axiom is the security property we assume about Ligero. It abstracts the combination of Ligero's low-degree test, linear constraint test, and quadratic constraint test into a single statement: if the verifier accepts, the committed witness satisfies the constraints.

This is an axiom (not proved) — filling it in requires formalizing Ligero's internals (Reed-Solomon, Merkle trees, proximity testing), which is a separate future spec.

## Component 3: Constraint Generation (Generate.lean)

The bridge between padded sumcheck and Ligero. After the sumcheck protocol runs, its transcript determines linear and quadratic constraints that any valid witness must satisfy.

### Definitions

```lean
/-- Generate linear constraints from a padded sumcheck transcript.
    Encodes: the sumcheck round polynomials telescope correctly,
    and the final evaluation matches the polynomial at the challenge point. -/
noncomputable def generateLinearConstraints
    (p : MultilinearPoly F nVars) (claimed_sum : F)
    (challenges : Fin nVars → F) :
    LinearConstraints F numLinConstraints witnessSize

/-- Generate quadratic constraints from the pad structure.
    Encodes: pad_left · pad_right = pad_product (pad consistency). -/
def generateQuadConstraints :
    Fin numQuadConstraints → QuadConstraint witnessSize
```

### Bridge theorem

```lean
/-- If a witness satisfies the generated constraints, then the
    original sumcheck claim is correct. This is the key bridge:
    constraint satisfaction → claim correctness. -/
theorem constraints_imply_correct
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (w : Fin witnessSize → F)
    (h_linear : satisfiesLinear w (generateLinearConstraints p claimed_sum challenges))
    (h_quad : ∀ i, satisfiesQuad w (generateQuadConstraints i)) :
    claimed_sum = ∑ b : Fin n → Bool, p.table b
```

This theorem says: the constraints are COMPLETE — they fully encode the sumcheck correctness condition. Any witness satisfying them implies the claimed sum is correct.

The proof unfolds the constraint definitions and shows they encode exactly the telescoping sum-check conditions from `verifierAccepts`, plus the pad consistency from the quadratic constraints.

**Note:** The exact definitions of `generateLinearConstraints` and `generateQuadConstraints` depend on how we encode the sumcheck transcript as a witness vector. The simplest encoding:
- Witness = `[round_0_poly_eval_at_0, round_0_poly_eval_at_1, ..., round_{n-1}_eval_at_0, round_{n-1}_eval_at_1, pad_0_eval_0, pad_0_eval_1, ...]`
- Linear constraint row i: encodes `eval_i(0) + eval_i(1) = previous_target`
- Quadratic constraints: encode `pad_left * pad_right = pad_product`

## Component 4: End-to-End Longfellow Soundness (Longfellow.lean)

### Verifier

```lean
/-- The Longfellow verifier: Ligero verification on constraints generated
    from the sumcheck transcript. -/
def longfellowVerifierAccepts [LigeroScheme F n m q]
    (p : MultilinearPoly F nVars) (claimed_sum : F)
    (challenges : Fin nVars → F)
    (ligeroCommit : LigeroScheme.Commitment)
    (ligeroProof : LigeroScheme.Proof) : Prop :=
  LigeroScheme.verify ligeroCommit
    (generateLinearConstraints p claimed_sum challenges)
    generateQuadConstraints
    ligeroProof
```

Note: the Longfellow verifier does NOT run the sumcheck verifier separately — the sumcheck correctness is encoded in the linear constraints that Ligero checks. This matches the IETF spec: the verifier only checks Ligero, and Ligero's constraints encode the sumcheck.

### Deterministic soundness

```lean
/-- If Ligero binding holds, the Longfellow verifier NEVER accepts a wrong claim.
    This is unconditional — no probability, no error term. -/
theorem longfellow_soundness_det [LigeroScheme F n m q]
    (p : MultilinearPoly F nVars) (claimed_sum : F)
    (w : Fin n → F)
    (challenges : Fin nVars → F)
    (ligeroProof : LigeroScheme.Proof)
    (haccept : longfellowVerifierAccepts p claimed_sum challenges
      (LigeroScheme.commit w) ligeroProof) :
    claimed_sum = ∑ b : Fin nVars → Bool, p.table b
```

**Proof:**
1. `haccept` gives `LigeroScheme.verify (commit w) lcs qcs π`
2. By `LigeroScheme.binding`: `satisfiesAll w lcs qcs`
3. By `constraints_imply_correct`: `claimed_sum = ∑ p.table`

Three lines.

### Probabilistic soundness

```lean
/-- Probabilistic Longfellow soundness: the probability of accepting
    a wrong claim equals the probability of breaking Ligero binding.
    
    In concrete Ligero instantiations, this is bounded by the proximity
    testing failure probability + collision resistance of the hash function. -/
theorem longfellow_soundness_prob [LigeroScheme F n m q]
    (p : MultilinearPoly F nVars) (claimed_sum : F)
    (hclaim : claimed_sum ≠ ∑ b, p.table b) :
    -- Any accepting proof requires a Ligero binding violation.
    -- The probability of this is ≤ LigeroScheme.soundnessError
    -- (parameterized, instantiated when Ligero internals are formalized).
    ∀ (w : Fin n → F) (π : LigeroScheme.Proof),
      ¬ longfellowVerifierAccepts p claimed_sum challenges
        (LigeroScheme.commit w) π
```

This is actually a COROLLARY of `longfellow_soundness_det` by contradiction: if the verifier accepted, `longfellow_soundness_det` gives `claimed_sum = ∑ p.table`, contradicting `hclaim`.

The probabilistic version with `countSat` is only needed when we instantiate `LigeroScheme` with a concrete (probabilistic) implementation. At the abstract level, binding is unconditional.

## Dependencies

### From existing codebase (no changes)
- `MultilinearPoly`, `eval`, `boolToField` — MLE
- `verifierAccepts`, `SumcheckRound` — Sumcheck protocol
- `sumcheck_soundness_det` — may be useful in `constraints_imply_correct`

### From Mathlib
- `Finset.sum`, `Fintype` — for linear constraint evaluation

## Expected Sorry's

- `constraints_imply_correct` — depends on the exact witness encoding. If the encoding is complex, this may need sorry for the most mechanical parts.
- `generateLinearConstraints` / `generateQuadConstraints` — the definitions themselves may be partial if the IETF spec's constraint format is hard to encode precisely.

## Non-Goals

- Ligero internals (Reed-Solomon, Merkle trees, proximity testing)
- Concrete `LigeroScheme` instantiation
- Zero-knowledge property
- Concrete hash function (SHA-256)
- Wire encoding / circuit compilation

## Future Work

Once this spec is implemented, the next specs would be:
1. **Reed-Solomon encoding** — polynomial evaluation, distance properties
2. **Merkle commitment** — abstract hash tree, authentication paths
3. **Concrete Ligero** — instantiate `LigeroScheme` with tableau + 3 tests
4. **Circuit model** — Longfellow's specific wire/gate representation

## References

- IETF draft-google-cfrg-libzk-01, Sections 4-6 (Ligero + constraint generation)
- Ames et al., "Ligero: Lightweight Sublinear Arguments" (CCS 2017)
- Existing lean-longfellow: MLE/, Sumcheck/, FiatShamir/
