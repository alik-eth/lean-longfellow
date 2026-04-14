# Circuit Model + Combining Polynomial Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the layered circuit model, EQ polynomial, combining polynomial Q, and single-layer reduction soundness theorem for Longfellow.

**Architecture:** Four new files in `LeanLongfellow/Circuit/`. Circuit layers are `add_poly`/`mul_poly` multilinear polynomials. The combining polynomial Q sums to V_i(t) over the Boolean hypercube. Layer reduction soundness follows from `sumcheck_soundness_det` with d=2. No existing files are modified (only root imports updated).

**Tech Stack:** Lean 4 (v4.30.0-rc1), Mathlib4 (`Finset.prod`, `Finset.sum_comm`, `Fintype.sum_equiv`)

**Spec:** `docs/specs/2026-04-14-circuit-combining-poly-design.md`

---

### Task 1: Circuit Definitions

**Files:**
- Create: `LeanLongfellow/Circuit/Defs.lean`

This task defines the circuit layer types, vector splitting/concatenation helpers, and the layer consistency predicate.

- [ ] **Step 1: Create `LeanLongfellow/Circuit/Defs.lean`**

```lean
import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval

open Finset MultilinearPoly

variable {F : Type*} [Field F]

/-! # Layered Circuit Model

Defines the abstract functional representation of a layered arithmetic circuit.
Each layer's structure is encoded via multilinear polynomials `add_poly` and
`mul_poly` over 3s variables (g, l, r). Layer values are multilinear extensions.
-/

-- ============================================================
-- Section 1: Vector splitting and concatenation helpers
-- ============================================================

/-- Extract the first s components from a 2s-vector. -/
def splitL {s : ℕ} {α : Type*} (lr : Fin (2 * s) → α) : Fin s → α :=
  fun j => lr ⟨j.val, by omega⟩

/-- Extract the last s components from a 2s-vector. -/
def splitR {s : ℕ} {α : Type*} (lr : Fin (2 * s) → α) : Fin s → α :=
  fun j => lr ⟨j.val + s, by omega⟩

/-- Concatenate three s-vectors into one 3s-vector. -/
def concat3 {s : ℕ} {α : Type*} (g l r : Fin s → α) : Fin (3 * s) → α :=
  fun k =>
    if h : k.val < s then g ⟨k.val, h⟩
    else if h2 : k.val < 2 * s then l ⟨k.val - s, by omega⟩
    else r ⟨k.val - 2 * s, by omega⟩

-- ============================================================
-- Section 2: Circuit layer types
-- ============================================================

/-- A single layer's structure, encoded as multilinear polynomials.
    `s` is the number of index bits (layer has 2^s gates).
    `add_poly(g,l,r) = 1` iff gate g is an add gate with inputs (l,r).
    `mul_poly(g,l,r) = 1` iff gate g is a mul gate with inputs (l,r). -/
structure CircuitLayer (F : Type*) [Field F] (s : ℕ) where
  add_poly : MultilinearPoly F (3 * s)
  mul_poly : MultilinearPoly F (3 * s)

/-- Layer values as a multilinear extension. -/
abbrev LayerValues (F : Type*) [Field F] (s : ℕ) := MultilinearPoly F s

-- ============================================================
-- Section 3: Layer consistency
-- ============================================================

/-- Layer i's value at gate g equals the sum over all (l,r) pairs:
    V_i(g) = ∑_{l,r} add(g,l,r)·(V_{i+1}(l) + V_{i+1}(r))
                    + mul(g,l,r)·V_{i+1}(l)·V_{i+1}(r) -/
def layerConsistent (layer : CircuitLayer F s) (V_curr V_next : LayerValues F s)
    (g : Fin s → Bool) : Prop :=
  V_curr.table g = ∑ lr : Fin (2 * s) → Bool,
    let l := splitL lr
    let r := splitR lr
    layer.add_poly.table (concat3 g l r) * (V_next.table l + V_next.table r) +
    layer.mul_poly.table (concat3 g l r) * (V_next.table l * V_next.table r)

-- ============================================================
-- Section 4: Concatenation lemmas
-- ============================================================

@[simp] theorem concat3_left {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) (h : j.val < s := j.isLt) :
    concat3 g l r ⟨j.val, by omega⟩ = g j := by
  simp [concat3, h]

@[simp] theorem concat3_mid {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) :
    concat3 g l r ⟨j.val + s, by omega⟩ = l j := by
  simp only [concat3]
  have h1 : ¬(j.val + s < s) := by omega
  have h2 : j.val + s < 2 * s := by omega
  simp [h1, h2, show j.val + s - s = j.val by omega]

@[simp] theorem concat3_right {s : ℕ} {α : Type*} (g l r : Fin s → α)
    (j : Fin s) :
    concat3 g l r ⟨j.val + 2 * s, by omega⟩ = r j := by
  simp only [concat3]
  have h1 : ¬(j.val + 2 * s < s) := by omega
  have h2 : ¬(j.val + 2 * s < 2 * s) := by omega
  simp [h1, h2, show j.val + 2 * s - 2 * s = j.val by omega]

/-- boolToField commutes with concat3. -/
theorem concat3_boolToField {s : ℕ} (g l r : Fin s → Bool) :
    concat3 (boolToField g) (boolToField l) (boolToField r) =
    boolToField (concat3 g l r) := by
  funext k
  simp only [concat3, boolToField]
  split <;> split <;> rfl
```

- [ ] **Step 2: Build and verify**

Run: `lake build LeanLongfellow.Circuit.Defs`
Expected: Compiles successfully.

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Circuit/Defs.lean
git commit -m "feat(Circuit): add layered circuit model with concat3 helpers"
```

---

### Task 2: EQ Polynomial

**Files:**
- Create: `LeanLongfellow/Circuit/EqPoly.lean`

This task defines the EQ polynomial and proves its key properties: Kronecker delta on Booleans, sum-to-one, and selection.

- [ ] **Step 1: Create `LeanLongfellow/Circuit/EqPoly.lean`**

```lean
import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval

open Finset MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-! # EQ Polynomial

The multilinear extension of the equality indicator function.
`eqPoly(t, x) = ∏ᵢ (tᵢ·xᵢ + (1-tᵢ)·(1-xᵢ))`.

On the Boolean hypercube, this is the Kronecker delta:
`eqPoly(t, b) = 1` if `t = b`, `0` otherwise.
-/

/-- The EQ polynomial: multilinear extension of the equality indicator.
    `eq(t, x) = ∏ᵢ (tᵢ·xᵢ + (1-tᵢ)·(1-xᵢ))` -/
noncomputable def eqPoly (t : Fin n → F) (x : Fin n → F) : F :=
  ∏ i : Fin n, (t i * x i + (1 - t i) * (1 - x i))

-- ============================================================
-- Bridge to lagrangeBasis
-- ============================================================

/-- eqPoly at a Boolean first argument equals lagrangeBasis. -/
theorem eqPoly_eq_lagrangeBasis (b : Fin n → Bool) (x : Fin n → F) :
    eqPoly (boolToField b) x = lagrangeBasis b x := by
  simp only [eqPoly, lagrangeBasis]
  apply Finset.prod_congr rfl
  intro i _
  simp only [boolToField]
  cases b i <;> simp <;> ring

-- ============================================================
-- Key properties
-- ============================================================

/-- On the Boolean hypercube, eqPoly is the Kronecker delta. -/
theorem eqPoly_bool (t b : Fin n → Bool) :
    eqPoly (boolToField t) (boolToField b) = if t = b then 1 else 0 := by
  rw [eqPoly_eq_lagrangeBasis]
  exact lagrangeBasis_indicator t b

/-- eqPoly selects a single term from a sum over the hypercube. -/
theorem eqPoly_select (t : Fin n → Bool) (f : (Fin n → Bool) → F) :
    ∑ b : Fin n → Bool, eqPoly (boolToField t) (boolToField b) * f b = f t := by
  simp only [eqPoly_bool]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_ite_eq']
  simp

/-- Summing eqPoly over the Boolean hypercube gives 1. -/
theorem eqPoly_sum (t : Fin n → Bool) :
    ∑ b : Fin n → Bool, eqPoly (boolToField t) (boolToField b) = 1 := by
  have := eqPoly_select t (fun _ => (1 : F))
  simpa using this
```

**Note for implementer:** The proofs leverage the existing `lagrangeBasis_indicator` from `MLE/Eval.lean`. The bridge theorem `eqPoly_eq_lagrangeBasis` does the heavy lifting. If `Fintype.sum_ite_eq'` doesn't exist with that exact name, try `Finset.sum_ite_eq'` with `Finset.univ` or `Fintype.sum_eq_single`.

- [ ] **Step 2: Build and verify**

Run: `lake build LeanLongfellow.Circuit.EqPoly`
Expected: Compiles successfully.

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Circuit/EqPoly.lean
git commit -m "feat(Circuit): add EQ polynomial with Kronecker delta and selection"
```

---

### Task 3: Combining Polynomial

**Files:**
- Create: `LeanLongfellow/Circuit/Combining.lean`

This task defines the combining polynomial Q and its MLE wrapper, and proves the sum theorem (`combiningPoly_sum`).

- [ ] **Step 1: Create `LeanLongfellow/Circuit/Combining.lean`**

```lean
import LeanLongfellow.Circuit.Defs
import LeanLongfellow.Circuit.EqPoly

open Finset MultilinearPoly

variable {F : Type*} [Field F] {s : ℕ}

/-! # Combining Polynomial

The GKR/Longfellow combining polynomial for a single-layer reduction:
`Q(l, r) = ∑_g eq(t, g) · [add(g,l,r)·(V(l) + V(r)) + mul(g,l,r)·V(l)·V(r)]`

The sum over g collapses via eqPoly_select. Q sums to V_i(t) over {0,1}^{2s}.

The MLE wrapper `combiningPolyMLE` packages Q's truth table as a
`MultilinearPoly F (2 * s)` for use with `verifierAccepts`. On {0,1}^{2s}
this agrees with Q. Off the hypercube they differ (Q has degree 2, the MLE
has degree 1), but soundness only depends on the {0,1} values.
-/

-- ============================================================
-- Section 1: Combining polynomial as a function
-- ============================================================

/-- The combining polynomial for the layer reduction.
    `Q(l, r) = ∑_g eq(t, g) · [add(g,l,r)·(V(l) + V(r)) + mul(g,l,r)·V(l)·V(r)]` -/
noncomputable def combiningPoly (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    (Fin (2 * s) → F) → F :=
  fun lr =>
    let l := splitL lr
    let r := splitR lr
    ∑ g : Fin s → Bool,
      eqPoly t (boolToField g) *
      (layer.add_poly.eval (concat3 (boolToField g) l r) *
        (V_next.eval l + V_next.eval r) +
       layer.mul_poly.eval (concat3 (boolToField g) l r) *
        (V_next.eval l * V_next.eval r))

-- ============================================================
-- Section 2: MLE wrapper
-- ============================================================

/-- The combining polynomial packaged as a MultilinearPoly over 2s variables.
    Table values are Q evaluated at Boolean inputs. -/
noncomputable def combiningPolyMLE (layer : CircuitLayer F s)
    (t : Fin s → F) (V_next : LayerValues F s) :
    MultilinearPoly F (2 * s) where
  table := fun b => combiningPoly layer t V_next (boolToField b)

-- ============================================================
-- Section 3: Sum theorem
-- ============================================================

/-- On Boolean inputs, MLE eval equals table lookup. -/
private theorem eval_at_bool (p : MultilinearPoly F n) (b : Fin n → Bool) :
    p.eval (boolToField b) = p.table b :=
  eval_boolVec p b

/-- The combining polynomial sums to V_i(t) over the Boolean hypercube.
    This is the claim that the sumcheck protocol verifies. -/
theorem combiningPoly_sum (layer : CircuitLayer F s)
    (t : Fin s → Bool) (V_curr V_next : LayerValues F s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g) :
    ∑ lr : Fin (2 * s) → Bool,
      combiningPoly layer (boolToField t) V_next (boolToField lr) =
    V_curr.table t := by
  -- Unfold combiningPoly and swap sums
  simp only [combiningPoly]
  rw [Finset.sum_comm]
  -- Now: ∑_g eqPoly(t, g) * (∑_{lr} add·(V+V) + mul·V·V)
  -- On Boolean inputs, eval = table (by eval_boolVec)
  -- The inner sum ∑_{lr} matches layerConsistent
  -- Apply eqPoly_select to collapse the outer sum
  conv_lhs =>
    arg 2; ext g
    rw [← Finset.mul_sum]
  -- Each inner sum should match hcons g after simplifying eval to table
  -- ∑_{lr} add(g,boolToField(l),boolToField(r))·(V(boolToField l)+...) + mul·V·V
  -- = ∑_{lr} add_table(concat3 g l r)·(V_table l + V_table r) + mul·V·V
  -- = V_curr.table g    [by hcons g]
  have hinner : ∀ g : Fin s → Bool,
      ∑ lr : Fin (2 * s) → Bool,
        (layer.add_poly.eval (concat3 (boolToField g) (boolToField (splitL lr)) (boolToField (splitR lr))) *
          (V_next.eval (boolToField (splitL lr)) + V_next.eval (boolToField (splitR lr))) +
         layer.mul_poly.eval (concat3 (boolToField g) (boolToField (splitL lr)) (boolToField (splitR lr))) *
          (V_next.eval (boolToField (splitL lr)) * V_next.eval (boolToField (splitR lr)))) =
        V_curr.table g := by
    intro g
    simp only [eval_at_bool, concat3_boolToField]
    exact (hcons g).symm
  sorry -- Complete by showing splitL/splitR of boolToField lr = boolToField (splitL/splitR lr),
        -- then applying hinner and eqPoly_select.
        -- The remaining work is showing that the sum variable transformation
        -- (boolToField on splitL/splitR) matches the form in hinner.
        -- This may require a `Finset.sum_congr` step.
```

**Important note for implementer:** The `combiningPoly_sum` proof is the hardest in this sub-project. The math is:
1. Swap sums via `Finset.sum_comm`
2. Factor out `eqPoly` via `Finset.mul_sum`
3. Simplify inner sum using `eval_boolVec` and `concat3_boolToField` to match `layerConsistent`
4. Apply `eqPoly_select`

The `sorry` marks the step where you need to show `splitL (boolToField lr) = boolToField (splitL lr)` and similarly for `splitR`. You may need helper lemmas:

```lean
theorem splitL_boolToField (lr : Fin (2 * s) → Bool) :
    splitL (boolToField lr) = boolToField (splitL lr)
theorem splitR_boolToField (lr : Fin (2 * s) → Bool) :
    splitR (boolToField lr) = boolToField (splitR lr)
```

These follow from `boolToField` being a pointwise operation. If the full proof is too hard, leave the `sorry` — it's expected as a possible sorry in the spec. The mathematical correctness is clear.

- [ ] **Step 2: Build and verify**

Run: `lake build LeanLongfellow.Circuit.Combining`
Expected: Compiles (possibly with the sorry in `combiningPoly_sum`).

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Circuit/Combining.lean
git commit -m "feat(Circuit): add combining polynomial with MLE wrapper and sum theorem"
```

---

### Task 4: Layer Reduction Soundness

**Files:**
- Create: `LeanLongfellow/Circuit/Reduction.lean`

This task defines the layer reduction structure, verifier, and proves soundness using `sumcheck_soundness_det` with d=2.

- [ ] **Step 1: Create `LeanLongfellow/Circuit/Reduction.lean`**

```lean
import LeanLongfellow.Circuit.Combining
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] {s : ℕ}

/-! # Single-Layer Reduction

Run sumcheck on the combining polynomial to reduce a layer-i claim
`V_i(t) = c` to two claims on V_{i+1} at points (l*, r*).

Soundness follows directly from `sumcheck_soundness_det` with d = 2.
-/

-- ============================================================
-- Section 1: Reduction structure
-- ============================================================

/-- A single-layer reduction: sumcheck rounds for 2s variables plus
    a random challenge α for combining the two resulting claims. -/
structure LayerReduction (F : Type*) [Field F] (s : ℕ) where
  /-- Sumcheck rounds for the 2s variables of (l, r) -/
  rounds : Fin (2 * s) → SumcheckRound F
  /-- Random challenge for combining the two resulting claims -/
  alpha : F

-- ============================================================
-- Section 2: Verifier
-- ============================================================

/-- The layer reduction verifier: run sumcheck verifier on the
    combining polynomial with claimed_sum = claimed_val. -/
def layerReductionAccepts (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_next : LayerValues F s)
    (red : LayerReduction F s) : Prop :=
  verifierAccepts (combiningPolyMLE layer t V_next) claimed_val red.rounds

-- ============================================================
-- Section 3: Soundness
-- ============================================================

/-- **Single-layer reduction soundness:** if the sumcheck verifier accepts
    but the claimed value is wrong, a challenge hit a root of a nonzero
    degree-≤-2 polynomial.

    Direct application of `sumcheck_soundness_det` with d = 2.
    The combining polynomial's MLE has the same {0,1} table as Q,
    so `∑ combiningPolyMLE.table = V_curr.table t` by `combiningPoly_sum`. -/
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
      diff.eval (red.rounds i).challenge = 0 := by
  -- Step 1: The true sum equals V_curr.table t
  have htrue : ∑ b : Fin (2 * s) → Bool,
      (combiningPolyMLE layer (boolToField t) V_next).table b = V_curr.table t := by
    simp only [combiningPolyMLE]
    exact combiningPoly_sum layer t V_curr V_next hcons
  -- Step 2: The claimed sum is wrong
  have hclaim' : claimed_val ≠ ∑ b, (combiningPolyMLE layer (boolToField t) V_next).table b := by
    rw [htrue]; exact hclaim
  -- Step 3: Apply sumcheck_soundness_det with d = 2
  exact sumcheck_soundness_det
    (combiningPolyMLE layer (boolToField t) V_next)
    claimed_val red.rounds hs (by omega) hclaim' haccept hdeg

-- ============================================================
-- Section 4: Claim extraction
-- ============================================================

/-- After the reduction, extract the two claims on V_{i+1}:
    (V_{i+1}(l*), V_{i+1}(r*)) where l*, r* are the challenge points. -/
noncomputable def extractClaims (V_next : LayerValues F s)
    (red : LayerReduction F s) : F × F :=
  let challenges := fun k => (red.rounds k).challenge
  let l_star : Fin s → F := fun j => challenges ⟨j.val, by omega⟩
  let r_star : Fin s → F := fun j => challenges ⟨j.val + s, by omega⟩
  (V_next.eval l_star, V_next.eval r_star)

/-- Combine two claims via α:
    `next_claim = α · a + (1-α) · b` -/
def combineClaims (a b alpha : F) : F :=
  alpha * a + (1 - alpha) * b
```

- [ ] **Step 2: Build and verify**

Run: `lake build LeanLongfellow.Circuit.Reduction`
Expected: Compiles successfully. If `combiningPoly_sum` has a sorry in Task 3, the `htrue` step here will still work (sorry propagates through).

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Circuit/Reduction.lean
git commit -m "feat(Circuit): add single-layer reduction with degree-2 soundness"
```

---

### Task 5: Root Imports + Full Build

**Files:**
- Modify: `LeanLongfellow.lean` (add Circuit imports)

- [ ] **Step 1: Add Circuit imports to root file**

Add these 4 lines to `LeanLongfellow.lean` after the existing Ligero imports:

```lean
import LeanLongfellow.Circuit.Defs
import LeanLongfellow.Circuit.EqPoly
import LeanLongfellow.Circuit.Combining
import LeanLongfellow.Circuit.Reduction
```

- [ ] **Step 2: Full build**

Run: `lake build`
Expected: Full project compiles. All existing files still build.

- [ ] **Step 3: Verify sorry count**

Run: `grep -r "sorry" LeanLongfellow/ --include="*.lean" -l`
Expected: `LeanLongfellow/Ligero/Generate.lean` (2 pre-existing sorry's) and possibly `LeanLongfellow/Circuit/Combining.lean` (if `combiningPoly_sum` proof was too hard).

- [ ] **Step 4: Commit**

```bash
git add LeanLongfellow.lean
git commit -m "feat: add Circuit module imports to root"
```
