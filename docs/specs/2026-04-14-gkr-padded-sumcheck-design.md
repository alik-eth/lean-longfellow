# GKR-Like Layered Circuit Reduction with Padded Sumcheck

**Date:** 2026-04-14
**Status:** Approved
**Depends on:** MLE (M2, complete), Sumcheck (M3-M4, complete), Fiat-Shamir (complete)

## Motivation

Longfellow uses a GKR-like protocol to verify layered arithmetic circuits. Each layer's correctness is reduced to a sumcheck claim about the previous layer, using quadratic gate constraints. The prover masks its messages with a one-time pad (the "padded sumcheck") for zero-knowledge. No mechanized proof of this reduction exists.

This design formalizes:
1. Longfellow's specific circuit structure (quadratic gates, MLE-based)
2. The single-layer sumcheck reduction
3. The padded sumcheck mechanism (soundness preservation + ZK statement)
4. End-to-end composition across all layers

## Approach

MLE-based representations throughout, connecting directly to the existing `MultilinearPoly` type. Circuit layers use quadratic constraints encoded as MLEs over `3k` variables (gate, left input, right input). The padded sumcheck is modeled as an algebraic mask on the prover's round polynomials. Soundness proofs reuse `sumcheck_soundness_det` directly.

### Longfellow's Circuit Structure

Unlike standard GKR (which uses separate add/multiply wiring predicates), Longfellow uses **quadratic constraints**:

```
V[j][g] = ∑_{l,r} Q[j][g,l,r] · V[j+1][l] · V[j+1][r]
```

where `Q[j]` is a sparse 3D coefficient array (the "quad"), `V[j]` are wire values at layer j, and the sum is over all input wire pairs `(l, r)`. This represents arbitrary circuits using only quadratic operations.

Source: IETF draft-google-cfrg-libzk-01.

## File Structure

```
LeanLongfellow/
├── GKR/
│   ├── Circuit.lean       # LayeredCircuit, LayerQuad, WireValues, layerConsistent
│   ├── Combining.lean     # combiningPoly, reduction to sumcheck
│   ├── LayerReduction.lean # layer_reduction_soundness theorem
│   ├── Pad.lean           # SumcheckPad, paddedMessage, padded_soundness_preserved
│   ├── PadZK.lean         # padded_zk statement (simulator existence)
│   └── Composition.lean   # gkr_soundness end-to-end theorem
```

## Component 1: Circuit Model (Circuit.lean)

### Types

```lean
/-- Quadratic constraints for a single layer, as an MLE over 3k variables.
    The 3k variables encode (gate : k, left_input : k, right_input : k). -/
structure LayerQuad (F : Type*) [Field F] (k : ℕ) where
  quad : MultilinearPoly F (3 * k)

/-- Wire values at a layer, as an MLE over k variables. -/
abbrev WireValues (F : Type*) [Field F] (k : ℕ) := MultilinearPoly F k

/-- A layered arithmetic circuit with `depth` layers, each having 2^k wires.
    Wire layer 0 = outputs, wire layer depth = inputs. -/
structure LayeredCircuit (F : Type*) [Field F] (k : ℕ) (depth : ℕ) where
  quads : Fin depth → LayerQuad F k
  wires : Fin (depth + 1) → WireValues F k
```

### Predicates

```lean
/-- Layer j is consistent at gate g: the quadratic constraint holds. -/
def layerConsistentAt (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (g : Fin k → F) : Prop :=
  (circuit.wires j).eval g =
  ∑ b_lr : Fin (2 * k) → Bool,
    (circuit.quads j).quad.eval (concat g (boolToField b_lr)) *
    (circuit.wires ⟨j + 1, by omega⟩).eval (extractLeft (boolToField b_lr)) *
    (circuit.wires ⟨j + 1, by omega⟩).eval (extractRight (boolToField b_lr))

/-- Layer j is fully consistent: the constraint holds at all Boolean gates. -/
def layerConsistent (circuit : LayeredCircuit F k depth) (j : Fin depth) : Prop :=
  ∀ g : Fin k → Bool, layerConsistentAt circuit j (boolToField g)

/-- A circuit is valid: all layers consistent and outputs are zero. -/
def circuitValid (circuit : LayeredCircuit F k depth) : Prop :=
  (∀ j, layerConsistent circuit j) ∧
  (∀ g : Fin k → Bool, (circuit.wires 0).eval (boolToField g) = 0)
```

Helper functions `concat`, `extractLeft`, `extractRight` manipulate `Fin (3*k)` and `Fin (2*k)` indices to split/join the `(g, l, r)` components. These use `Fin.append`, `Fin.castAdd`, `Fin.natAdd`.

## Component 2: Combining Polynomial (Combining.lean)

The GKR reduction works by fixing a random evaluation point `g*` and constructing a polynomial whose sum over `{0,1}^{2k}` equals `V[j](g*)`:

```lean
/-- The combining polynomial for the GKR sumcheck at layer j.
    Given a random point g*, this is a (2k)-variate MLE:
    f(l, r) = Q[j](g*, l, r) · V[j+1](l) · V[j+1](r) -/
noncomputable def combiningPoly (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F) : MultilinearPoly F (2 * k) where
  table b_lr :=
    let l := extractLeftBool b_lr
    let r := extractRightBool b_lr
    (circuit.quads j).quad.eval (concat gStar (boolToField b_lr)) *
    (circuit.wires ⟨j + 1, by omega⟩).eval (boolToField l) *
    (circuit.wires ⟨j + 1, by omega⟩).eval (boolToField r)
```

### Key theorem

```lean
/-- The combining polynomial's hypercube sum equals V[j](g*) when the layer
    is consistent. This is why the sumcheck claim is correct. -/
theorem combiningPoly_sum (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (gStar : Fin k → F) (hcons : layerConsistentAt circuit j gStar) :
    ∑ b : Fin (2 * k) → Bool, (combiningPoly circuit j gStar).table b =
      (circuit.wires j).eval gStar
```

## Component 3: Single-Layer Reduction (LayerReduction.lean)

### Main theorem

```lean
/-- Single-layer reduction soundness: if the sumcheck verifier accepts the
    combining polynomial with claimed sum V[j](g*), but the layer is NOT
    consistent at g*, then some challenge is a root of a nonzero degree-≤-1
    polynomial. -/
theorem layer_reduction_soundness
    (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (gStar : Fin k → F) (rounds : Fin (2 * k) → SumcheckRound F)
    (hn : 0 < 2 * k)
    (haccept : verifierAccepts (combiningPoly circuit j gStar)
      ((circuit.wires j).eval gStar) rounds)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_inconsistent : ¬ layerConsistentAt circuit j gStar) :
    ∃ i, ∃ diff, diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (rounds i).challenge = 0
```

**Proof:** Direct application of `sumcheck_soundness_det`. The claimed sum `V[j](g*)` differs from the actual hypercube sum `∑ combiningPoly.table` because the layer is inconsistent (by contraposition of `combiningPoly_sum`). The rest is exactly our existing interactive soundness.

### MLE uniqueness connection

```lean
/-- The verifier's random g* catches inconsistency with high probability.
    If a layer is inconsistent (fails at some Boolean gate), then a random
    g* in F^k will detect it with probability ≥ 1 - k/|F| (by MLE uniqueness:
    if the MLE of V[j] differs from the MLE of the correct values, they
    disagree at a random point with high probability). -/
theorem random_gstar_detects (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (h_inconsistent : ¬ layerConsistent circuit j) :
    countSat (fun gStar : Fin k → F =>
      ¬ layerConsistentAt circuit j gStar) ≥
      Fintype.card F ^ k - Fintype.card F ^ (k - 1)
```

This uses `mle_unique`: two MLEs agreeing on all Boolean points agree everywhere. Contrapositive: if they disagree at some Boolean point, a random field point detects it.

## Component 4: Padded Sumcheck (Pad.lean)

### Types

```lean
/-- A sumcheck pad: random masking polynomials committed before the protocol. -/
structure SumcheckPad (F : Type*) [Field F] (n : ℕ) where
  masks : Fin n → Polynomial F

/-- Padded round message: original polynomial minus pad. -/
def paddedMessage (original pad : Polynomial F) : Polynomial F :=
  original - pad

/-- Padded rounds: apply padding to each round's prover polynomial. -/
def paddedRounds (rounds : Fin n → SumcheckRound F) (pad : SumcheckPad F n) :
    Fin n → SumcheckRound F :=
  fun i => ⟨paddedMessage (rounds i).prover_poly (pad.masks i), (rounds i).challenge⟩
```

### Theorems

```lean
/-- Padding preserves the verifier's checks: the pad cancels in the sum
    g(0) + g(1) because (g-p)(0) + (g-p)(1) = g(0)+g(1) - (p(0)+p(1)),
    and the same pad offset appears on both sides of each check.

    IMPORTANT: This requires a "consistent pad" condition — the pad values
    must satisfy the same telescoping structure as the honest polynomials.
    Specifically: pad_i(0) + pad_i(1) = pad_{i-1}(r_{i-1}) for each round. -/
theorem padded_soundness_preserved
    (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (pad : SumcheckPad F n)
    (h_pad_consistent : ∀ i : Fin n,
      (pad.masks i).eval 0 + (pad.masks i).eval 1 =
        if (i : ℕ) = 0 then (∑ j, (pad.masks j).eval 0)  -- pad's claimed sum offset
        else (pad.masks ⟨i - 1, by omega⟩).eval (rounds ⟨i - 1, by omega⟩).challenge) :
    verifierAccepts p claimed_sum (paddedRounds rounds pad) ↔
    verifierAccepts p (claimed_sum + pad_sum_offset) rounds
```

Note: the exact formulation of pad consistency depends on how Longfellow structures the pad commitment. The key property is that padding transforms one valid sumcheck transcript into another, preserving the accept/reject decision up to a known offset in the claimed sum.

### Simpler alternative formulation

If the pad consistency condition is too complex, use this cleaner version:

```lean
/-- If the verifier accepts padded rounds, there exist unpadded rounds
    that the verifier would also accept with the same challenges. -/
theorem padded_to_unpadded
    (rounds_padded : Fin n → SumcheckRound F)
    (pad : SumcheckPad F n) :
    verifierAccepts p c (paddedRounds rounds_unpadded pad) →
    verifierAccepts p c rounds_unpadded
```

This follows if padding preserves `eval 0 + eval 1` (which it does when the pad satisfies the telescoping condition) and preserves the final evaluation check.

## Component 5: Zero-Knowledge Statement (PadZK.lean)

```lean
/-- Zero-knowledge: there exists a simulator that, given only the claimed sum
    and challenges (no witness/circuit knowledge), produces padded round
    polynomials with the same distribution as the real padded prover. -/
theorem padded_zk
    (real_rounds : Fin n → SumcheckRound F)
    (hdeg : ∀ i, (real_rounds i).prover_poly.natDegree ≤ d) :
    ∃ simulator : (Fin n → F) → SumcheckPad F n → (Fin n → Polynomial F),
      ∀ (pad : SumcheckPad F n) (challenges : Fin n → F),
        -- For each round, the simulated padded message has the same distribution
        -- as the real padded message, over the uniform choice of pad
        ∀ i, (simulator challenges pad i) has same distribution as
             (paddedMessage (real_rounds i).prover_poly (pad.masks i))
```

The simulator constructs: for each round, choose a random polynomial of degree ≤ d satisfying the sum constraint, then subtract the pad. Since the pad is uniform and independent, the result is uniform — matching the real distribution.

**This theorem may require sorry.** The distributional equality requires either a probability monad or a counting argument showing the preimage sizes match. It's the hardest theorem in this formalization.

## Component 6: End-to-End Composition (Composition.lean)

```lean
/-- GKR end-to-end soundness for a depth-d circuit with 2^k wires per layer.

    The total number of random challenges is:
    - k challenges for g* at each layer (except input layer)
    - 2k challenges per sumcheck (one per round)
    Total: depth * (k + 2k) = depth * 3k challenges

    Probability of accepting an invalid circuit ≤ depth * 3k / |F|. -/
theorem gkr_soundness (circuit : LayeredCircuit F k depth)
    (h_invalid : ¬ circuitValid circuit)
    (hn : 0 < k)
    (cs : Fin (depth * 3 * k) → F) -- all challenges flattened
    (all_rounds : ...) -- per-layer sumcheck rounds
    (hdeg : ...) -- degree bounds
    :
    countSat (fun cs => gkr_accepts circuit cs) ≤
      depth * (3 * k) * Fintype.card F ^ (depth * 3 * k - 1)
```

**Proof:** By induction on `depth`:
- Base case (depth = 0): no layers, `circuitValid` reduces to output check only.
- Inductive step: apply `layer_reduction_soundness` for layer 0, then use `random_gstar_detects` for the g* selection, and apply the IH for layers 1..depth-1. Union bound over all challenges.

## Dependencies

### From existing codebase (no changes)
- `MultilinearPoly`, `eval`, `boolToField`, `lagrangeBasis` — MLE layer
- `verifierAccepts`, `honestProver` — sumcheck protocol
- `sumcheck_soundness_det` — interactive soundness
- `sumcheck_completeness` — interactive completeness
- `mle_unique` — for random g* detection
- `countSat`, `countSat_union_bound`, `countSat_root_hit` — probability counting

### From Mathlib
- `Fin.append`, `Fin.castAdd`, `Fin.natAdd` — index manipulation for (g, l, r)
- `Fintype`, `Finset.card` — counting

## Non-Goals

- Ligero commitment scheme formalization
- Concrete circuit compilation (ECDSA, SHA-256 circuits)
- Optimizations (parallel-prefix, sparse quad representation)
- Fiat-Shamir composition with GKR (already covered by existing `fiatShamir_soundness`)

## Expected Sorry's

- `padded_zk` (ZK statement) — distributional equality is hard without a probability monad. Having the statement is still valuable.
- Potentially some `Fin` index manipulation lemmas in the `(g, l, r)` decomposition.

## References

- IETF draft-google-cfrg-libzk-01, Sections 3-4 (circuit structure, padded sumcheck)
- Goldwasser-Kalai-Rothblum, "Delegating Computation" (STOC 2008)
- Thaler, "A Note on the GKR Protocol" (2013)
- Cormode-Mitzenmacher-Thaler, "Practical Verified Computation" (CRYPTO 2012)
