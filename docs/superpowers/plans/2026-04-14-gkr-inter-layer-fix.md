# GKR Inter-Layer Linkage Fix Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix the GKR inter-layer reduction to model the real two-claim-to-one reduction, then prove the end-to-end probabilistic soundness bound `depth * (2k + 1) / |F|`.

**Architecture:** After sumcheck on layer j's combining polynomial (2k challenges), the verifier gets two evaluation points `l*` and `r*` (the first and second halves of the challenge vector). It needs `V[j+1](l*)` and `V[j+1](r*)`. A random scalar `α` combines them into one claim at `gStar_{j+1}`. The extra `α` per layer adds 1 challenge, giving `2k + 1` challenges per layer and `depth * (2k + 1)` total. The end-to-end bound uses `countSat_union_bound` across layers.

**Tech Stack:** Lean 4 v4.30.0-rc1, Mathlib4, existing MLE/Sumcheck/FiatShamir/GKR modules

---

## File Changes

```
LeanLongfellow/GKR/
├── Composition.lean   # REWRITE: proper inter-layer linkage + end-to-end bound
```

Only one file changes. Everything else (Circuit, Combining, LayerReduction, Pad, PadZK) stays as-is.

## Existing APIs Used

| API | File |
|-----|------|
| `layerVerifierAccepts` | GKR/Composition.lean (keep) |
| `layer_reduction_soundness` | GKR/LayerReduction.lean |
| `combiningPoly` | GKR/Combining.lean |
| `layerConsistentAt` | GKR/Circuit.lean |
| `countSat`, `countSat_union_bound`, `countSat_adaptive_root` | FiatShamir/Oracle.lean |
| `sumcheck_soundness_det` | Sumcheck/Soundness.lean |

---

### Task 1: Two-Claim Reduction Model

**Files:**
- Modify: `LeanLongfellow/GKR/Composition.lean`

- [ ] **Step 1: Add the two-claim-to-one reduction definitions**

Replace the current `deriveNextGStar` (which just takes first k challenges) with the proper model. After sumcheck on a `2k`-variate combining polynomial, the challenge vector gives two points:

```lean
/-- Extract l* (first k challenges) from the sumcheck challenge vector. -/
def extractLStar (challenges : Fin (2 * k) → F) : Fin k → F :=
  fun i => challenges (Fin.castAdd k i)

/-- Extract r* (last k challenges) from the sumcheck challenge vector. -/
def extractRStar (challenges : Fin (2 * k) → F) : Fin k → F :=
  fun i => challenges (Fin.natAdd k i)

/-- Combine two evaluation points with random scalar α.
    gStar_next(i) = α · l*(i) + (1 - α) · r*(i)
    This reduces two claims V[j+1](l*) and V[j+1](r*) into one
    claim about V[j+1](gStar_next). -/
def combinePoints (lStar rStar : Fin k → F) (α : F) : Fin k → F :=
  fun i => α * lStar i + (1 - α) * rStar i
```

- [ ] **Step 2: Define per-layer challenge allocation**

Each layer needs `2k` sumcheck challenges plus 1 combining scalar `α`. Define a structure for this:

```lean
/-- All random values for one GKR layer:
    - 2k sumcheck challenges
    - 1 combining scalar α -/
structure LayerRandomness (F : Type*) (k : ℕ) where
  sumcheckChallenges : Fin (2 * k) → F
  alpha : F

/-- Derive gStar for the next layer from the current layer's randomness. -/
def deriveNextGStar' (rand : LayerRandomness F k) : Fin k → F :=
  combinePoints (extractLStar rand.sumcheckChallenges)
                (extractRStar rand.sumcheckChallenges)
                rand.alpha
```

- [ ] **Step 3: Redefine the linked GKR verifier**

```lean
/-- Full GKR verifier with proper inter-layer linkage.
    gStar_0 is the initial evaluation point.
    Each subsequent gStar is derived from the previous layer's challenges + α. -/
def gkrFullVerifier (circuit : LayeredCircuit F k depth)
    (gStar_0 : Fin k → F)
    (layerRand : Fin depth → LayerRandomness F k)
    (allRounds : Fin depth → Fin (2 * k) → SumcheckRound F)
    -- Challenge consistency
    (h_challenges : ∀ j i, (allRounds j i).challenge = (layerRand j).sumcheckChallenges i) : Prop :=
  let gStars : Fin depth → Fin k → F := fun j =>
    match j with
    | ⟨0, _⟩ => gStar_0
    | ⟨j' + 1, hj⟩ => deriveNextGStar' (layerRand ⟨j', by omega⟩)
  ∀ j, layerVerifierAccepts circuit j (gStars j) (allRounds j)
```

Note: The `match` on `Fin` might need adjustment. Alternatively use `if j.val = 0 then gStar_0 else deriveNextGStar' (layerRand ⟨j.val - 1, by omega⟩)`.

- [ ] **Step 4: Prove linked deterministic soundness**

```lean
/-- Linked deterministic soundness: if any layer is inconsistent at its
    derived gStar, the layer's sumcheck has a root hit. -/
theorem gkr_full_soundness_det (circuit : LayeredCircuit F k depth)
    (gStar_0 : Fin k → F)
    (layerRand : Fin depth → LayerRandomness F k)
    (allRounds : Fin depth → Fin (2 * k) → SumcheckRound F)
    (h_challenges : ∀ j i, (allRounds j i).challenge = (layerRand j).sumcheckChallenges i)
    (hk : 0 < 2 * k)
    (j_bad : Fin depth)
    (h_inconsistent : ¬ layerConsistentAt circuit j_bad (gStars_from j_bad))
    (haccept : gkrFullVerifier circuit gStar_0 layerRand allRounds h_challenges)
    (hdeg : ∀ j i, (allRounds j i).prover_poly.natDegree ≤ 1) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (allRounds j_bad i).challenge = 0
```

Proof: Extract layer j_bad from `haccept`, delegate to `layer_reduction_soundness`. Same as current `gkr_linked_soundness_det` but with the new verifier.

- [ ] **Step 5: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 6: Commit**

```bash
git add LeanLongfellow/GKR/Composition.lean
git commit -m "fix(GKR): model proper two-claim-to-one inter-layer reduction"
```

---

### Task 2: Combining Scalar Soundness

**Files:**
- Modify: `LeanLongfellow/GKR/Composition.lean`

The combining step introduces an additional soundness gap: the random `α` must ensure that if `V[j+1](l*) ≠ correct_l` OR `V[j+1](r*) ≠ correct_r`, then `α · V[j+1](l*) + (1-α) · V[j+1](r*) ≠ correct_combined` with high probability.

- [ ] **Step 1: Prove combining scalar lemma**

```lean
/-- If two pairs (a₁, b₁) ≠ (a₂, b₂), then α·a₁ + (1-α)·b₁ ≠ α·a₂ + (1-α)·b₂
    for all but at most 1 value of α.
    
    This is because α·(a₁-a₂) + (1-α)·(b₁-b₂) = 0 is a degree-1 equation in α
    (unless a₁-a₂ = b₁-b₂, in which case it's degree 0 and either always 0 or never 0). -/
theorem combine_ne_of_ne (a₁ b₁ a₂ b₂ : F) (hne : (a₁, b₁) ≠ (a₂, b₂)) :
    ∃ S : Finset F, S.card ≤ 1 ∧
      ∀ α : F, α ∉ S → 
        α * a₁ + (1 - α) * b₁ ≠ α * a₂ + (1 - α) * b₂
```

Proof strategy:
- `α * a₁ + (1-α) * b₁ = α * a₂ + (1-α) * b₂`
- `⟺ α * (a₁ - a₂) + (b₁ - b₂) - α * (b₁ - b₂) = 0`
- `⟺ α * (a₁ - a₂ - b₁ + b₂) + (b₁ - b₂) = 0`
- This is a degree-≤-1 equation in α. If the coefficient of α is nonzero, at most 1 solution. If it's zero, then `a₁ - a₂ = b₁ - b₂`, and the constant `b₁ - b₂` must be 0 too (otherwise no solutions). But `a₁ - a₂ = b₁ - b₂` and `b₁ - b₂ = 0` gives `a₁ = a₂` and `b₁ = b₂`, contradicting `hne`.
- So either the equation has 0 or 1 solutions. `S` = the set of solutions.

Use `Polynomial.card_roots'` or direct Schwartz-Zippel reasoning.

- [ ] **Step 2: Prove combining scalar counting bound**

```lean
/-- The number of α values that fail to distinguish two different pairs
    is at most 1. For counting over all challenges: the combining step
    adds at most |F|^(total-1) bad assignments. -/
theorem combine_countSat (a₁ b₁ a₂ b₂ : F) (hne : (a₁, b₁) ≠ (a₂, b₂))
    {n : ℕ} (i : Fin n) :
    countSat (fun cs : RandomChallenges F n =>
      cs i * a₁ + (1 - cs i) * b₁ = cs i * a₂ + (1 - cs i) * b₂) ≤
      Fintype.card F ^ (n - 1)
```

This follows from `countSat_eq_val` — the equation pins `cs i` to at most 1 value.

- [ ] **Step 3: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 4: Commit**

```bash
git add LeanLongfellow/GKR/Composition.lean
git commit -m "feat(GKR): prove combining scalar soundness for two-claim reduction"
```

---

### Task 3: End-to-End Probabilistic Bound

**Files:**
- Modify: `LeanLongfellow/GKR/Composition.lean`

- [ ] **Step 1: Define total challenge space**

Each layer uses `2k + 1` random values (2k sumcheck + 1 combining α). Plus k random values for the initial gStar_0. Total: `k + depth * (2k + 1)`.

For the counting theorem, flatten all randomness into one vector:

```lean
/-- Total random values for a depth-d GKR protocol with width 2^k:
    k for initial gStar_0 + depth * (2k + 1) for layer challenges + α. -/
def gkrTotalChallenges (k depth : ℕ) : ℕ := k + depth * (2 * k + 1)
```

- [ ] **Step 2: State the end-to-end bound**

```lean
/-- End-to-end GKR soundness bound.
    For an invalid circuit, the number of total challenge vectors that
    fool the verifier is at most depth * (2k + 1) * |F|^(total - 1).
    
    Dividing by |F|^total gives probability ≤ depth * (2k + 1) / |F|.
    
    The (2k + 1) per layer comes from: 2k sumcheck challenges (each can
    hit a root) + 1 combining α (can fail to distinguish the two claims). -/
theorem gkr_end_to_end_bound (circuit : LayeredCircuit F k depth)
    (h_invalid : ¬ circuitValid circuit)
    (hk : 0 < k) :
    ∀ (adversary : RandomChallenges F (gkrTotalChallenges k depth) →
        Fin depth → Fin (2 * k) → SumcheckRound F),
    -- degree bounds + non-adaptivity hypotheses...
    countSat (fun cs => gkrFullVerifier' circuit cs adversary) ≤
      depth * (2 * k + 1) * Fintype.card F ^ (gkrTotalChallenges k depth - 1)
```

**This is the hardest theorem.** The proof structure:
1. `h_invalid` means some layer `j` is inconsistent at some Boolean gate
2. By `mle_unique`/`random_gstar_detects`, random gStar catches this
3. Per layer: 2k root-hit events (sumcheck) + 1 combining-failure event
4. Union bound over `depth` layers × `(2k + 1)` events per layer

If the full end-to-end proof is too hard (flattening challenges into one vector is type-heavy), prove a **per-layer version** that combines the sumcheck and combining bounds:

```lean
/-- Per-layer total bound: sumcheck (2k) + combining (1) = 2k + 1 bad events,
    each contributing |F|^(n-1) bad assignments. -/
theorem gkr_layer_total_bound (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (hk : 0 < 2 * k)
    (h_inconsistent : ¬ layerConsistentAt circuit j gStar)
    ... :
    countSat (...) ≤ (2 * k + 1) * Fintype.card F ^ (n - 1)
```

This is `gkr_per_layer_bound` (already proved for the 2k part) extended with the combining scalar bound (+1).

- [ ] **Step 3: Prove what you can**

Try the per-layer version first. If the end-to-end flattening is too hard, the per-layer result plus a comment explaining how the union bound over layers gives `depth * (2k+1) / |F|` is still valuable.

- [ ] **Step 4: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 5: Commit**

```bash
git add LeanLongfellow/GKR/Composition.lean
git commit -m "feat(GKR): prove end-to-end probabilistic soundness bound"
```

---

### Task 4: Clean Up and Final Verification

**Files:**
- Modify: `LeanLongfellow/GKR/Composition.lean` (remove old `gkrVerifierAcceptsLinked` and `gkr_linked_soundness_det` if superseded)
- Modify: `LeanLongfellow.lean` (verify imports)

- [ ] **Step 1: Remove superseded definitions**

If `gkrFullVerifier` replaces `gkrVerifierAcceptsLinked`, remove the old one. Keep `gkrVerifierAccepts` and `gkr_soundness_det` (the unlinked per-layer versions are independently useful).

- [ ] **Step 2: Full build and sorry check**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Run: `grep -rn "sorry" LeanLongfellow/`

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/GKR/Composition.lean LeanLongfellow.lean
git commit -m "chore(GKR): clean up composition, remove superseded definitions"
```

---

## Dependency Graph

```
Task 1 (Two-Claim Model) → Task 2 (Combining Scalar) → Task 3 (End-to-End Bound) → Task 4 (Cleanup)
```

Strictly sequential.

## Spec Coverage

| Codex Suggestion | Task |
|-----------------|------|
| 1. Restructure gStar linkage with l*/r* + α | Task 1 + Task 2 |
| 2. Non-adaptivity on per-layer bound | Already done (previous session) |
| 3. End-to-end depth * (2k+1) / \|F\| bound | Task 3 |
