# Circuit Model + Combining Polynomial + Layer Reduction

**Date:** 2026-04-14
**Status:** Approved
**Depends on:** MLE (complete), Sumcheck (complete, generalized to degree ≤ d)
**Sub-project:** B of A/B/C (degree-d generalization / circuit+combining / concrete Ligero)

## Motivation

Longfellow's sumcheck operates on a combining polynomial `Q·V·V` that produces degree-2 round polynomials. Sub-project A generalized the sumcheck infrastructure to degree ≤ d. This sub-project builds the circuit model and combining polynomial that instantiate `d = 2`, connecting the abstract sumcheck to Longfellow's concrete arithmetic.

## Key Design Decisions

1. **Abstract functional circuit model** — Layers encoded as multilinear polynomials `add_poly`/`mul_poly` over `3s` variables `(g, l, r)`. No gate/wire types or serialization.

2. **EQ polynomial as standalone module** — `eq(x,y) = ∏(xᵢyᵢ + (1-xᵢ)(1-yᵢ))` with Kronecker delta and selection properties. Reusable beyond the circuit context.

3. **Single-layer reduction only** — Prove one sumcheck step reduces a layer-i claim to two layer-(i+1) claims. Full recursive composition is a corollary by induction, deferred.

4. **No padding or ZK** — Padding and the ZK simulator are orthogonal to soundness. Deferred to sub-project C (concrete Ligero).

5. **No modifications to existing files** — Circuit module is purely additive. Only change is new imports in `LeanLongfellow.lean`.

## File Structure

```
LeanLongfellow/
├── Circuit/
│   ├── Defs.lean        # CircuitLayer, LayerValues, layerConsistent
│   ├── EqPoly.lean      # eqPoly, Kronecker delta, selection theorem
│   ├── Combining.lean   # combiningPoly, sum theorem, degree-2 property
│   └── Reduction.lean   # LayerReduction, layerReductionAccepts, soundness
```

## Component 1: Circuit Model (Defs.lean)

### Types

```lean
/-- A single layer's structure, encoded as multilinear polynomials.
    `s` is the number of index bits (layer has 2^s gates).
    `add_poly(g,l,r) = 1` iff gate g is an add gate with inputs (l,r).
    `mul_poly(g,l,r) = 1` iff gate g is a mul gate with inputs (l,r). -/
structure CircuitLayer (F : Type*) [Field F] (s : ℕ) where
  add_poly : MultilinearPoly F (3 * s)
  mul_poly : MultilinearPoly F (3 * s)

/-- Layer values as a multilinear extension. -/
abbrev LayerValues (F : Type*) [Field F] (s : ℕ) := MultilinearPoly F s
```

### Layer consistency

```lean
/-- Layer i's value at gate g equals the sum over all (l,r) pairs:
    V_i(g) = ∑_{l,r} add(g,l,r)·(V_{i+1}(l) + V_{i+1}(r))
                    + mul(g,l,r)·V_{i+1}(l)·V_{i+1}(r) -/
def layerConsistent (layer : CircuitLayer F s) (V_curr V_next : LayerValues F s)
    (g : Fin s → Bool) : Prop :=
  V_curr.table g = ∑ lr : Fin (2 * s) → Bool,
    let l := fun j => lr ⟨j, by omega⟩
    let r := fun j => lr ⟨j + s, by omega⟩
    let glr := concat3 g l r
    layer.add_poly.table glr * (V_next.table l + V_next.table r) +
    layer.mul_poly.table glr * (V_next.table l * V_next.table r)
```

The concatenation `Fin.append` for `Fin (3*s)` from `Fin s`, `Fin s`, `Fin s` needs a helper. Define:

```lean
/-- Concatenate three Boolean vectors into one over 3*s bits. -/
def concat3 {s : ℕ} (g l r : Fin s → Bool) : Fin (3 * s) → Bool :=
  fun k =>
    if h : k.val < s then g ⟨k.val, h⟩
    else if h2 : k.val < 2 * s then l ⟨k.val - s, by omega⟩
    else r ⟨k.val - 2 * s, by omega⟩
```

Similarly for field elements:

```lean
/-- Concatenate three field-element vectors into one over 3*s variables. -/
def concat3F {s : ℕ} (g l r : Fin s → F) : Fin (3 * s) → F :=
  fun k =>
    if h : k.val < s then g ⟨k.val, h⟩
    else if h2 : k.val < 2 * s then l ⟨k.val - s, by omega⟩
    else r ⟨k.val - 2 * s, by omega⟩
```

## Component 2: EQ Polynomial (EqPoly.lean)

### Definition

```lean
/-- The EQ polynomial: multilinear extension of the equality indicator.
    eq(x, y) = ∏ᵢ (xᵢ·yᵢ + (1-xᵢ)·(1-yᵢ)) -/
noncomputable def eqPoly {n : ℕ} (t : Fin n → F) (x : Fin n → F) : F :=
  ∏ i : Fin n, (t i * x i + (1 - t i) * (1 - x i))
```

### Properties

```lean
/-- On the Boolean hypercube, eqPoly is the Kronecker delta. -/
theorem eqPoly_bool (t b : Fin n → Bool) :
    eqPoly (boolToField t) (boolToField b) = if t = b then 1 else 0

/-- Summing eqPoly over the Boolean hypercube gives 1. -/
theorem eqPoly_sum (t : Fin n → F) :
    ∑ b : Fin n → Bool, eqPoly t (boolToField b) = 1

/-- eqPoly selects a single term from a sum over the hypercube. -/
theorem eqPoly_select (t : Fin n → Bool) (f : (Fin n → Bool) → F) :
    ∑ b : Fin n → Bool, eqPoly (boolToField t) (boolToField b) * f b = f t
```

**Proof strategy for `eqPoly_bool`:** Induction on `n`. The product factors into independent per-coordinate terms. Each factor is `bᵢ·tᵢ + (1-bᵢ)(1-tᵢ)` which equals 1 when `bᵢ = tᵢ` and 0 otherwise (using `boolToField` values 0/1). The product is 1 iff all factors are 1, i.e., `b = t`.

**Proof strategy for `eqPoly_select`:** Follows from `eqPoly_bool`: the sum becomes `∑ b, (if t = b then 1 else 0) * f b`, and only the `b = t` term survives.

## Component 3: Combining Polynomial (Combining.lean)

### Definition

```lean
/-- The combining polynomial for the GKR/Longfellow layer reduction.
    Q(l, r) = ∑_g eq(t, g) · [add(g,l,r)·(V(l) + V(r)) + mul(g,l,r)·V(l)·V(r)]
    where the sum over g collapses (via eqPoly_select) to a single gate. -/
noncomputable def combiningPoly (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    (Fin (2 * s) → F) → F :=
  fun lr =>
    let l := fun j => lr ⟨j, by omega⟩
    let r := fun j => lr ⟨j + s, by omega⟩
    ∑ g : Fin s → Bool,
      eqPoly t (boolToField g) *
      (layer.add_poly.eval (concat3F (boolToField g) l r) *
        (V_next.eval l + V_next.eval r) +
       layer.mul_poly.eval (concat3F (boolToField g) l r) *
        (V_next.eval l * V_next.eval r))
```

### Packaging as MultilinearPoly

To feed the combining polynomial into `verifierAccepts`, we need it as a `MultilinearPoly F (2 * s)`:

```lean
/-- The combining polynomial packaged as a MultilinearPoly over 2s variables.
    The table is computed by evaluating combiningPoly on all Boolean inputs. -/
noncomputable def combiningPolyMLE (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    MultilinearPoly F (2 * s) where
  table := fun b => combiningPoly layer t V_next (boolToField b)
```

This works because `MultilinearPoly` is defined by its truth table, and the MLE is uniquely determined by its values on `{0,1}^{2s}`.

### Key theorems

```lean
/-- The combining polynomial sums to V_i(t) over the Boolean hypercube. -/
theorem combiningPoly_sum (layer : CircuitLayer F s)
    (t : Fin s → Bool) (V_curr V_next : LayerValues F s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g) :
    ∑ lr : Fin (2 * s) → Bool,
      combiningPoly layer (boolToField t) V_next (boolToField lr) =
    V_curr.table t
```

**Proof:** Swap sums (∑_{lr} ∑_g → ∑_g ∑_{lr}), apply `eqPoly_select` to collapse the g sum, then the inner sum matches `layerConsistent`.

**Note on degree-2:** The combining polynomial Q has degree 2 per variable (from the `mul·V·V` term), but `combiningPolyMLE` is a `MultilinearPoly` (degree 1 per variable by construction). These agree on `{0,1}^{2s}` but differ elsewhere. This is fine for soundness: the adversary's round polynomials may have degree ≤ 2 (hypothesis `hdeg`), while the honest MLE prover has degree ≤ 1. The diff has degree ≤ max(2,1) = 2, and `sumcheck_soundness_det` with `d = 2` gives the root hit. No degree-2 honest prover construction is needed for the soundness proof.

## Component 4: Single-Layer Reduction (Reduction.lean)

### Types

```lean
/-- A single-layer reduction: sumcheck rounds for 2s variables plus
    a random challenge α for combining the two resulting claims. -/
structure LayerReduction (F : Type*) [Field F] (s : ℕ) where
  rounds : Fin (2 * s) → SumcheckRound F
  alpha : F
```

### Verifier

```lean
/-- The layer reduction verifier: run sumcheck verifier on the
    combining polynomial with claimed_sum = claimed_val. -/
def layerReductionAccepts (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_next : LayerValues F s)
    (red : LayerReduction F s) : Prop :=
  verifierAccepts (combiningPolyMLE layer t V_next) claimed_val red.rounds
```

### Soundness

```lean
/-- Single-layer reduction soundness: if the sumcheck verifier accepts
    but the claimed value is wrong, a challenge hit a degree-≤-2 root.
    Direct application of sumcheck_soundness_det with d = 2. -/
theorem layer_reduction_soundness (layer : CircuitLayer F s)
    (t : Fin s → Bool) (claimed_val : F)
    (V_curr V_next : LayerValues F s)
    (red : LayerReduction F s)
    (hs : 0 < 2 * s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g)
    (hclaim : claimed_val ≠ V_curr.table t)
    (haccept : layerReductionAccepts layer (boolToField t) claimed_val V_next red)
    (hdeg : ∀ i, (red.rounds i).prover_poly.natDegree ≤ 2) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval (red.rounds i).challenge = 0
```

**Proof:**
1. `combiningPoly_sum` + `hcons` gives: `∑ lr, combiningPolyMLE.table lr = V_curr.table t`
2. `hclaim` gives: `claimed_val ≠ ∑ lr, combiningPolyMLE.table lr`
3. `sumcheck_soundness_det` with `d = 2`, `hd := by omega` gives the root hit

Three lines.

### Claim extraction

```lean
/-- After the reduction, extract the two claims on V_{i+1}. -/
def extractClaims (layer : CircuitLayer F s) (t : Fin s → F)
    (V_next : LayerValues F s) (red : LayerReduction F s) :
    F × F :=
  let challenges := fun k => (red.rounds k).challenge
  let l_star := fun j => challenges ⟨j, by omega⟩
  let r_star := fun j => challenges ⟨j + s, by omega⟩
  (V_next.eval l_star, V_next.eval r_star)

/-- Combine two claims via α:
    next_claim = α · V(l*) + (1-α) · V(r*) -/
def combineClaims (a b alpha : F) : F :=
  alpha * a + (1 - alpha) * b
```

## Dependencies

### From existing codebase (no changes)
- `MultilinearPoly`, `eval`, `boolToField`, `lagrangeBasis` — MLE module
- `SumcheckRound`, `verifierAccepts` — Sumcheck/Protocol
- `sumcheck_soundness_det` with `d = 2` — Sumcheck/Soundness (generalized in sub-project A)
- `sumFirstVar`, `sumFirstVar_natDegree_le` — MLE/Props

### From Mathlib
- `Finset.prod`, `Finset.sum` — for eqPoly and combining polynomial
- `Fintype.sum_congr`, `Finset.sum_comm` — for proof of combiningPoly_sum

## Expected Sorry's

1. **Possible:** `concat3` / `concat3F` interaction lemmas — showing that `concat3 (boolToField g) (boolToField l) (boolToField r) = boolToField (concat3 g l r)` and similar. Tedious index arithmetic, may need sorry if Lean's `omega`/`simp` can't close the goals.

2. **Possible:** `combiningPoly_sum` — the proof requires swapping sums and matching the `layerConsistent` definition through `concat3`. The math is straightforward but the Lean bookkeeping may be nontrivial.

**Sorry-free targets:** `eqPoly_bool`, `eqPoly_sum`, `eqPoly_select`, `layer_reduction_soundness` (direct application of `sumcheck_soundness_det`).

## Non-Goals

- Full recursive GKR composition (corollary by induction, deferred)
- Padded sumcheck / ZK simulator (sub-project C)
- Concrete Ligero internals (sub-project C)
- Circuit serialization (IETF spec §12)
- Specific field instantiations
