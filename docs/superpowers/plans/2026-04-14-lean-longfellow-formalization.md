# Lean Longfellow Formalization Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize Longfellow's multilinear extension (MLE) and sumcheck protocol in Lean 4, producing mechanized completeness and soundness proofs.

**Architecture:** Table-based MLE representation (`(Fin n → Bool) → F`) with Mathlib field axioms. Multilinearity is a derived property of the evaluation function, not an axiom in the structure. This simplifies construction and avoids the spec's incorrect linearity axioms (which describe linear, not affine, functions — the MLE is affine in each variable). The sumcheck protocol uses first-variable-first ordering with `partialEvalFirst` for clean inductive structure.

**Tech Stack:** Lean 4 v4.30.0-rc1, Mathlib4 (master), Lake build system

**Design deviation from spec:** The spec puts `is_additive` and `is_homogeneous` axioms in the `MultilinearPoly` structure. These axioms describe *linear* functions (f(0)=0), but the multilinear extension is *affine* in each variable (e.g., `(1-x)(1-y)` is not linear). This plan uses a table-based representation instead: `MultilinearPoly` stores only the evaluation table on `{0,1}^n`, and multilinearity of the extension is a *theorem* about the `eval` function, not an axiom. All spec theorems are preserved; only the structure definition changes.

---

## File Structure

```
LeanLongfellow/
├── MLE/
│   ├── Defs.lean          # MultilinearPoly structure, lagrangeBasis, boolToField
│   ├── Eval.lean          # eval, partialEvalFirst, sumFirstVar, key lemmas
│   ├── Extension.lean     # mle_unique, mle_extension_exists
│   └── Props.lean         # mle_sum_hypercube, degree bounds
├── Sumcheck/
│   ├── Protocol.lean      # SumcheckRound, verifierAccepts, honestProver
│   ├── Completeness.lean  # sumcheck_completeness, sumcheck_round_reduce
│   └── Soundness.lean     # sumcheck_soundness (Schwartz-Zippel application)
└── Field/
    └── Basic.lean         # ZMod instantiation, #eval integration tests
```

Root import file: `LeanLongfellow.lean` (updated in Task 10)

---

### Task 1: MLE Core Types

**Files:**
- Create: `LeanLongfellow/MLE/Defs.lean`

- [ ] **Step 1: Create `MLE/Defs.lean` with structure and helpers**

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset

/-- A multilinear polynomial over `n` variables with coefficients in `F`.
    Represented as its evaluation table over `{0,1}^n`. -/
structure MultilinearPoly (F : Type*) [Field F] (n : ℕ) where
  /-- Values at all Boolean points in `{0,1}^n`. -/
  table : (Fin n → Bool) → F

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Cast a Boolean assignment to field elements: `true ↦ 1`, `false ↦ 0`. -/
def boolToField (b : Fin n → Bool) : Fin n → F :=
  fun i => if b i then 1 else 0

/-- Lagrange basis polynomial for Boolean vector `b`, evaluated at point `x`.
    `lagrangeBasis b x = ∏ᵢ (bᵢ · xᵢ + (1 - bᵢ) · (1 - xᵢ))` -/
def lagrangeBasis (b : Fin n → Bool) (x : Fin n → F) : F :=
  ∏ i : Fin n, if b i then x i else 1 - x i

end MultilinearPoly
```

- [ ] **Step 2: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds (Mathlib cache already downloaded).

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/MLE/Defs.lean
git commit -m "feat(MLE): add MultilinearPoly structure, lagrangeBasis, boolToField"
```

---

### Task 2: MLE Evaluation

**Files:**
- Create: `LeanLongfellow/MLE/Eval.lean`

- [ ] **Step 1: Create `MLE/Eval.lean` with `eval` and theorem stubs**

```lean
import LeanLongfellow.MLE.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.VecNotation

open Finset Polynomial

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Evaluate the multilinear extension at any point `x ∈ F^n`.
    `eval p x = ∑_{b ∈ {0,1}^n} p.table(b) · lagrangeBasis(b, x)` -/
def eval (p : MultilinearPoly F n) (x : Fin n → F) : F :=
  ∑ b : Fin n → Bool, p.table b * lagrangeBasis b x

/-- The Lagrange basis at a Boolean point is the Kronecker delta. -/
theorem lagrangeBasis_indicator (b b' : Fin n → Bool) :
    lagrangeBasis (F := F) b (boolToField b') = if b = b' then 1 else 0 := by
  sorry

/-- Evaluating the MLE at a Boolean point recovers the table entry. -/
theorem eval_boolVec (p : MultilinearPoly F n) (b : Fin n → Bool) :
    p.eval (boolToField b) = p.table b := by
  sorry

end MultilinearPoly
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds with warnings about `sorry`.

- [ ] **Step 3: Prove `lagrangeBasis_indicator`**

Strategy:
- Unfold `lagrangeBasis` and `boolToField`.
- **Case `b = b'`:** Every factor is `1` (when `b i = true`, `boolToField b' i = 1`; when `b i = false`, `1 - boolToField b' i = 1 - 0 = 1`). Use `Finset.prod_eq_one`.
- **Case `b ≠ b'`:** There exists `i` with `b i ≠ b' i`. That factor is `0`. Use `Finset.prod_eq_zero`.
- Case split on `b i` and `b' i` with `cases (b i) <;> cases (b' i) <;> simp`.

- [ ] **Step 4: Prove `eval_boolVec`**

Strategy:
- Unfold `eval`. Apply `lagrangeBasis_indicator` inside the sum.
- Use `Finset.sum_eq_single b` to collapse: the `b' = b` term gives `p.table b * 1`; all other terms give `p.table b' * 0 = 0`.

- [ ] **Step 5: Verify proofs compile without sorry**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds, no `sorry` warnings.

- [ ] **Step 6: Commit**

```bash
git add LeanLongfellow/MLE/Eval.lean
git commit -m "feat(MLE): add eval function, prove lagrangeBasis_indicator and eval_boolVec"
```

---

### Task 3: MLE Partial Evaluation and Restriction

**Files:**
- Modify: `LeanLongfellow/MLE/Eval.lean`

- [ ] **Step 1: Add `partialEvalFirst` and `sumFirstVar` with theorem stubs**

Append to `Eval.lean`, inside the `MultilinearPoly` namespace:

```lean
/-- Fix the first variable to `a`, yielding an `n`-variate MLE.
    Table entry: `(1 - a) · p.table(false :: b) + a · p.table(true :: b)`. -/
def partialEvalFirst (p : MultilinearPoly F (n + 1)) (a : F) : MultilinearPoly F n where
  table b := (1 - a) * p.table (Fin.cons false b) + a * p.table (Fin.cons true b)

/-- Sum over all but the first variable, producing a univariate polynomial.
    This is the honest prover's message in each sumcheck round.
    `sumFirstVar p = C(c₀) + X · C(c₁ - c₀)` where
    `c₀ = ∑_b p.table(0::b)`, `c₁ = ∑_b p.table(1::b)`. -/
def sumFirstVar (p : MultilinearPoly F (n + 1)) : F[X] :=
  let c0 := ∑ b : Fin n → Bool, p.table (Fin.cons false b)
  let c1 := ∑ b : Fin n → Bool, p.table (Fin.cons true b)
  C c0 + X * C (c1 - c0)

/-- `sumFirstVar(p)` evaluated at 0 gives `∑_b p.table(false :: b)`. -/
theorem sumFirstVar_eval_zero (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 0 = ∑ b : Fin n → Bool, p.table (Fin.cons false b) := by
  sorry

/-- `sumFirstVar(p)` evaluated at 1 gives `∑_b p.table(true :: b)`. -/
theorem sumFirstVar_eval_one (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 1 = ∑ b : Fin n → Bool, p.table (Fin.cons true b) := by
  sorry

/-- The partial evaluation's table sum equals `sumFirstVar` evaluated at the challenge.
    This is the key round-reduction lemma for sumcheck. -/
theorem partialEval_table_sum (p : MultilinearPoly F (n + 1)) (r : F) :
    (∑ b : Fin n → Bool, (partialEvalFirst p r).table b) = (sumFirstVar p).eval r := by
  sorry

/-- Evaluating the partial evaluation equals evaluating the original with `r` prepended. -/
theorem partialEvalFirst_eval (p : MultilinearPoly F (n + 1)) (r : F) (x : Fin n → F) :
    (partialEvalFirst p r).eval x = p.eval (Fin.cons r x) := by
  sorry

/-- Lagrange basis factors: `lagrangeBasis (Fin.cons b₀ b) (Fin.cons a x)
    = (if b₀ then a else 1 - a) * lagrangeBasis b x`. -/
theorem lagrangeBasis_cons (b₀ : Bool) (b : Fin n → Bool) (a : F) (x : Fin n → F) :
    lagrangeBasis (Fin.cons b₀ b) (Fin.cons a x) =
      (if b₀ then a else 1 - a) * lagrangeBasis b x := by
  sorry
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds with `sorry` warnings.

- [ ] **Step 3: Prove `sumFirstVar_eval_zero` and `sumFirstVar_eval_one`**

Strategy: Unfold `sumFirstVar`, simplify `Polynomial.eval` using `eval_add`, `eval_mul`, `eval_C`, `eval_X`. At `X = 0`: the `X * C(c1 - c0)` term vanishes. At `X = 1`: `C c0 + 1 * C(c1 - c0) = c0 + c1 - c0 = c1`.

- [ ] **Step 4: Prove `lagrangeBasis_cons`**

Strategy:
- Unfold `lagrangeBasis` as `∏ i : Fin (n+1), ...`.
- Use `Fin.prod_univ_succ` (or `Fin.prod_cons`) to split into `(term at 0) * ∏ i : Fin n, (term at i+1)`.
- Show `Fin.cons b₀ b 0 = b₀` and `Fin.cons b₀ b (Fin.succ i) = b i` (and same for `a`/`x`).
- The remaining product is `lagrangeBasis b x`.

- [ ] **Step 5: Prove `partialEval_table_sum`**

Strategy:
- Unfold `partialEvalFirst` table.
- Distribute the sum: `∑_b ((1-r) * p.table(false::b) + r * p.table(true::b))` = `(1-r) * ∑_b p.table(false::b) + r * ∑_b p.table(true::b)`.
- Use `Finset.sum_add_distrib` and `Finset.mul_sum`.
- Show this equals `c0 + r * (c1 - c0)` = `(sumFirstVar p).eval r`.

- [ ] **Step 6: Prove `partialEvalFirst_eval`**

Strategy:
- Expand both sides as sums over `Fin n → Bool` (LHS) and `Fin (n+1) → Bool` (RHS).
- Use a bijection: `Fin (n+1) → Bool ≃ Bool × (Fin n → Bool)` via `Fin.cons`.
- Apply `lagrangeBasis_cons` to factor each term.
- Rearrange using `Finset.sum_product'` or `Finset.sum_comm`.
- The sums match after distributing `(1-r)` and `r` terms.

- [ ] **Step 7: Verify all proofs compile without sorry**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds, no `sorry` warnings in `Eval.lean`.

- [ ] **Step 8: Commit**

```bash
git add LeanLongfellow/MLE/Eval.lean
git commit -m "feat(MLE): add partialEvalFirst, sumFirstVar, prove round-reduction lemmas"
```

---

### Task 4: MLE Uniqueness

**Files:**
- Create: `LeanLongfellow/MLE/Extension.lean`

- [ ] **Step 1: Create `Extension.lean` with theorem stubs**

```lean
import LeanLongfellow.MLE.Eval

open Finset

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Two multilinear polynomials with the same evaluation table are equal. -/
theorem mle_unique (p q : MultilinearPoly F n) (h : p.table = q.table) :
    ∀ x : Fin n → F, p.eval x = q.eval x := by
  sorry

/-- Any function on `{0,1}^n` has a unique multilinear extension.
    Specifically, for any `f : (Fin n → Bool) → F`, the polynomial `⟨f⟩`
    is the unique MLE that agrees with `f` on the Boolean hypercube. -/
theorem mle_extension_exists (f : (Fin n → Bool) → F) :
    ∃! p : MultilinearPoly F n, ∀ b, p.eval (boolToField b) = f b := by
  sorry

end MultilinearPoly
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `mle_unique`**

Strategy: Trivial — `eval` is defined purely in terms of `table`, so `h : p.table = q.table` gives `p.eval x = q.eval x` by `congr`.

```lean
theorem mle_unique (p q : MultilinearPoly F n) (h : p.table = q.table) :
    ∀ x : Fin n → F, p.eval x = q.eval x := by
  intro x
  simp only [eval, h]
```

- [ ] **Step 4: Prove `mle_extension_exists`**

Strategy:
- **Existence:** The witness is `⟨f⟩`. By `eval_boolVec`, `⟨f⟩.eval (boolToField b) = f b`.
- **Uniqueness:** If `p.eval (boolToField b) = f b` for all `b`, then by `eval_boolVec`, `p.table b = f b` for all `b`. So `p.table = f`, meaning `p = ⟨f⟩`.

Key subtlety: we need `eval_boolVec` to go from "agrees on Boolean points" to "tables are equal." Since `eval_boolVec` says `p.eval (boolToField b) = p.table b`, if `p.eval (boolToField b) = f b`, then `p.table b = f b`.

- [ ] **Step 5: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 6: Commit**

```bash
git add LeanLongfellow/MLE/Extension.lean
git commit -m "feat(MLE): prove mle_unique and mle_extension_exists"
```

---

### Task 5: MLE Properties

**Files:**
- Create: `LeanLongfellow/MLE/Props.lean`

- [ ] **Step 1: Create `Props.lean` with theorem stubs**

```lean
import LeanLongfellow.MLE.Eval
import Mathlib.Algebra.Polynomial.Degree.Definitions

open Finset Polynomial

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- The sum of a multilinear polynomial over the Boolean hypercube
    equals the sum of its evaluation table. -/
theorem mle_sum_hypercube (p : MultilinearPoly F n) :
    ∑ b : Fin n → Bool, p.eval (boolToField b) = ∑ b : Fin n → Bool, p.table b := by
  sorry

/-- The honest prover polynomial has degree ≤ 1. -/
theorem sumFirstVar_natDegree_le (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).natDegree ≤ 1 := by
  sorry

/-- The sum of `sumFirstVar(p)` at 0 and 1 equals the full table sum. -/
theorem sumFirstVar_sum (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 0 + (sumFirstVar p).eval 1 =
      ∑ b : Fin (n + 1) → Bool, p.table b := by
  sorry

end MultilinearPoly
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `mle_sum_hypercube`**

Strategy: Direct application of `eval_boolVec` under `Finset.sum_congr`.

```lean
theorem mle_sum_hypercube (p : MultilinearPoly F n) :
    ∑ b : Fin n → Bool, p.eval (boolToField b) = ∑ b : Fin n → Bool, p.table b := by
  apply Finset.sum_congr rfl
  intro b _
  exact eval_boolVec p b
```

- [ ] **Step 4: Prove `sumFirstVar_natDegree_le`**

Strategy:
- `sumFirstVar p = C c0 + X * C (c1 - c0)`.
- This is a polynomial of the form `a + b * X` which has degree ≤ 1.
- Use `natDegree_add_le`, `natDegree_C`, `natDegree_mul_le`, `natDegree_X`.

- [ ] **Step 5: Prove `sumFirstVar_sum`**

Strategy:
- Use `sumFirstVar_eval_zero` and `sumFirstVar_eval_one` from Task 3.
- `∑_b p.table(false::b) + ∑_b p.table(true::b)` = `∑_{b' : Fin (n+1) → Bool} p.table b'`.
- The last step splits the sum over `Fin (n+1) → Bool` by the first coordinate. Use a lemma that decomposes `∑_{b' : Fin (n+1) → Bool}` into `∑_{b₀ : Bool} ∑_{b : Fin n → Bool}` via `Fin.cons`. This may require `Fintype.sum_prod_type'` or `Equiv.sum_comp` with the equivalence `(Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool)`.

- [ ] **Step 6: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 7: Commit**

```bash
git add LeanLongfellow/MLE/Props.lean
git commit -m "feat(MLE): prove mle_sum_hypercube, sumFirstVar degree bound and sum identity"
```

---

### Task 6: Sumcheck Protocol Model

**Files:**
- Create: `LeanLongfellow/Sumcheck/Protocol.lean`

- [ ] **Step 1: Create `Protocol.lean` with protocol types and verifier**

```lean
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Props
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Polynomial MultilinearPoly

/-- A single round of the sumcheck protocol. -/
structure SumcheckRound (F : Type*) [Field F] where
  /-- Prover sends a univariate polynomial -/
  prover_poly : F[X]
  /-- Verifier sends a random challenge -/
  challenge : F

variable {F : Type*} [Field F] {n : ℕ}

/-- The verifier's accept predicate for the sumcheck protocol.
    Given a polynomial `p`, claimed sum `c`, and `n` rounds of interaction:
    1. Round 0: `g₀(0) + g₀(1) = c`
    2. Round i+1: `gᵢ₊₁(0) + gᵢ₊₁(1) = gᵢ(rᵢ)`
    3. Final: `gₙ₋₁(rₙ₋₁) = p.eval(r₀, r₁, ..., rₙ₋₁)` -/
def verifierAccepts (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F) : Prop :=
  -- Sum check: each round polynomial sums to the previous round's evaluation
  (∀ i : Fin n,
    (rounds i).prover_poly.eval 0 + (rounds i).prover_poly.eval 1 =
      if (i : ℕ) = 0 then claimed_sum
      else (rounds ⟨i.val - 1, by omega⟩).prover_poly.eval
            (rounds ⟨i.val - 1, by omega⟩).challenge) ∧
  -- Final evaluation check
  (0 < n →
    let last : Fin n := ⟨n - 1, by omega⟩
    (rounds last).prover_poly.eval (rounds last).challenge =
      p.eval (fun i => (rounds i).challenge))

/-- Construct the honest prover's rounds recursively.
    In each round, send `sumFirstVar` of the current (partially evaluated) polynomial,
    then partially evaluate at the verifier's challenge. -/
def honestRounds : (challenges : Fin n → F) → MultilinearPoly F n → (Fin n → SumcheckRound F)
  | challenges, p => fun i => by
    -- Build rounds sequentially: at round i, the polynomial has been partially
    -- evaluated i times. We define a helper to compute the i-th partial evaluation.
    exact sorry -- Defined properly in Step 3

/-- Helper: apply `i` rounds of partial evaluation. -/
def applyPartialEvals (p : MultilinearPoly F (n + m)) (challenges : Fin m → F) :
    MultilinearPoly F n := by
  exact sorry -- Defined in Step 3
```

- [ ] **Step 2: Verify stub compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Replace stubs with concrete definitions**

The cleanest approach defines the honest prover recursively. Replace the stubs with:

```lean
/-- Apply `partialEvalFirst` repeatedly, fixing the first `k` variables. -/
def iterPartialEval : {m : ℕ} → MultilinearPoly F m → (Fin m → F) → (k : ℕ) → (hk : k ≤ m) →
    MultilinearPoly F (m - k)
  | _, p, _, 0, _ => by rwa [Nat.sub_zero]
  | m + 1, p, challenges, k + 1, hk => by
    rw [show m + 1 - (k + 1) = m - k from by omega]
    exact iterPartialEval (p.partialEvalFirst (challenges ⟨0, by omega⟩))
      (fun i => challenges ⟨i.val + 1, by omega⟩) k (by omega)

/-- The honest prover's round-`i` polynomial: `sumFirstVar` of the polynomial
    after `i` rounds of partial evaluation. -/
def honestRoundPoly (p : MultilinearPoly F (n + 1)) (challenges : Fin (n + 1) → F)
    (i : Fin (n + 1)) : F[X] :=
  -- After i partial evaluations, we have an (n + 1 - i)-variate polynomial.
  -- sumFirstVar extracts the next univariate round polynomial.
  sorry

/-- The honest prover for the sumcheck protocol. -/
def honestProver (p : MultilinearPoly F n) (challenges : Fin n → F) :
    Fin n → SumcheckRound F :=
  fun i => ⟨honestRoundPoly sorry sorry i, challenges i⟩  -- placeholder
```

Note: The exact recursive definition of `honestRoundPoly` requires careful dependent-type juggling (`n + 1 - i` as an index). The implementer should consider defining it via an auxiliary inductive construction or using `Fin.cases` / recursion on `i`. An alternative approach is to avoid the recursive definition entirely and define the honest prover non-recursively using `iterPartialEval`:

```lean
/-- Honest prover's polynomial at round i. After fixing variables 0..i-1 to
    their challenges, compute sumFirstVar of the remaining polynomial.
    Requires casting: the remaining polynomial has (n - i) variables,
    and sumFirstVar needs (n - i) = ((n - i - 1) + 1). -/
noncomputable def honestRoundPoly (p : MultilinearPoly F n) (challenges : Fin n → F)
    (i : Fin n) : F[X] := by
  have h : n - i.val = (n - i.val - 1) + 1 := by omega
  let p_i : MultilinearPoly F (n - i.val) := iterPartialEval p challenges i.val (le_of_lt i.isLt)
  exact (h ▸ p_i).sumFirstVar

noncomputable def honestProver (p : MultilinearPoly F n) (challenges : Fin n → F) :
    Fin n → SumcheckRound F :=
  fun i => ⟨honestRoundPoly p challenges i, challenges i⟩
```

The `noncomputable` is needed because `Field F` operations are generally noncomputable in Lean.

- [ ] **Step 4: Verify definitions compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 5: Commit**

```bash
git add LeanLongfellow/Sumcheck/Protocol.lean
git commit -m "feat(Sumcheck): add protocol model, verifier predicate, honest prover"
```

---

### Task 7: Sumcheck Completeness

**Files:**
- Create: `LeanLongfellow/Sumcheck/Completeness.lean`

- [ ] **Step 1: Create `Completeness.lean` with theorem stubs**

```lean
import LeanLongfellow.Sumcheck.Protocol

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Each round reduces an n-variate sum claim to an (n-1)-variate sum claim.
    Specifically: `sumFirstVar(p).eval(r) = ∑_b (partialEvalFirst p r).table b`. -/
theorem sumcheck_round_reduce (p : MultilinearPoly F (n + 1)) (r : F) :
    (sumFirstVar p).eval r = ∑ b : Fin n → Bool, (partialEvalFirst p r).table b :=
  (partialEval_table_sum p r).symm

/-- **Sumcheck completeness:** if the claimed sum is correct and the prover is honest,
    the verifier always accepts. Error probability = 0. -/
theorem sumcheck_completeness (p : MultilinearPoly F n)
    (challenges : Fin n → F) :
    verifierAccepts p (∑ b : Fin n → Bool, p.table b) (honestProver p challenges) := by
  sorry
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `sumcheck_completeness`**

Strategy — prove both conjuncts of `verifierAccepts`:

**Conjunct 1 (sum checks):** By induction/cases on `i`:
- `i = 0`: `g₀(0) + g₀(1)` = sum of partially evaluated table = total sum. Use `sumFirstVar_sum`.
- `i > 0`: `gᵢ(0) + gᵢ(1)` = sum of `iterPartialEval` after `i` steps = `g_{i-1}(r_{i-1})`. Use `sumcheck_round_reduce` applied to the polynomial after `i-1` partial evaluations.

**Conjunct 2 (final eval):** The last round polynomial evaluated at `r_{n-1}` should equal `p.eval(challenges)`. This follows from `partialEvalFirst_eval` applied `n` times: evaluating the fully-partially-evaluated polynomial (a 0-variable MLE, which is just a constant) equals `p.eval(challenges)`.

Key helper lemma to prove first:

```lean
/-- After all partial evaluations, the remaining 0-variable polynomial's
    table value equals `p.eval(challenges)`. -/
theorem iterPartialEval_full (p : MultilinearPoly F n) (challenges : Fin n → F) :
    (iterPartialEval p challenges n le_rfl).table (Fin.elim0) =
      p.eval (fun i => challenges i) := by
  sorry
```

This is proved by induction on `n`, using `partialEvalFirst_eval` at each step.

- [ ] **Step 4: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 5: Commit**

```bash
git add LeanLongfellow/Sumcheck/Completeness.lean
git commit -m "feat(Sumcheck): prove sumcheck_completeness"
```

---

### Task 8: Sumcheck Soundness

**Files:**
- Create: `LeanLongfellow/Sumcheck/Soundness.lean`

- [ ] **Step 1: Create `Soundness.lean` with theorem stubs**

```lean
import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import Mathlib.Algebra.Polynomial.Roots

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- A nonzero polynomial of degree ≤ 1 has at most 1 root in any set `S`.
    Follows from Mathlib's `Polynomial.card_roots'`. -/
theorem roots_le_one_of_deg_le_one {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1)
    (S : Finset F) :
    (S.filter (fun r => p.eval r = 0)).card ≤ 1 := by
  sorry

/-- **Sumcheck soundness (deterministic form):**
    If the verifier accepts but the claimed sum is wrong, then at least one
    round polynomial differs from the honest one, and the challenge for that
    round is a root of their difference (a nonzero polynomial of degree ≤ 1). -/
theorem sumcheck_soundness_det (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds) :
    ∃ i : Fin n,
      rounds i ≠ honestProver p (fun j => (rounds j).challenge) i ∧
      ∃ (diff : F[X]), diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
        diff.eval (rounds i).challenge = 0 := by
  sorry

/-- **Sumcheck soundness (counting form):**
    The number of challenge vectors `(r₀, ..., r_{n-1}) ∈ S^n` for which
    *any* cheating prover can fool the verifier is at most `n · |S|^{n-1}`.
    This gives probability bound `n / |S|` (= `n · 1 / |S|` for degree-1 polys). -/
theorem sumcheck_soundness (p : MultilinearPoly F n) (claimed_sum : F) (S : Finset F)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (round_polys : Fin n → F[X])
    (hdeg : ∀ i, (round_polys i).natDegree ≤ 1) :
    (S.piFinset (fun _ => S) |>.filter fun challenges =>
      verifierAccepts p claimed_sum (fun i => ⟨round_polys i, challenges i⟩)).card
    ≤ n * S.card ^ (n - 1) := by
  sorry
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Note: The `piFinset` usage may need adjustment — check `Fintype.piFinset` vs `Finset.pi` in current Mathlib. Adjust the statement if needed.

- [ ] **Step 3: Prove `roots_le_one_of_deg_le_one`**

Strategy:
- A polynomial with `natDegree ≤ 1` has at most 1 root (it's either constant or linear).
- From Mathlib: `Polynomial.card_roots' p` gives `p.roots.card ≤ p.natDegree`.
- The roots in `S` form a subset of `p.roots` (viewed as a multiset), so `(S.filter ...).card ≤ p.roots.card ≤ p.natDegree ≤ 1`.
- Need `IsDomain F`, which follows from `Field F`.

- [ ] **Step 4: Prove `sumcheck_soundness_det`**

Strategy — by induction on `n`, analyzing where the prover first deviates:

**Base case `n = 0`:** `verifierAccepts` for 0 rounds means `claimed_sum = p.table (Fin.elim0)` (vacuously, or depending on formulation). But `hclaim` says they differ. Contradiction, so the `∃` is vacuously true (no `Fin 0`).

**Inductive step `n + 1`:** From `verifierAccepts`, round 0 satisfies:
- `g₀(0) + g₀(1) = claimed_sum`

The honest prover would send `sumFirstVar p`, which satisfies `g₀_honest(0) + g₀_honest(1) = actual_sum`.

Since `claimed_sum ≠ actual_sum`, either:
- **`g₀ ≠ g₀_honest`:** Then `g₀ - g₀_honest` is nonzero with degree ≤ 1. The verifier's challenge `r₀` must satisfy a consistency check that constrains it. If `(g₀ - g₀_honest).eval r₀ = 0`, we found our witness at `i = 0`.
- **`g₀ = g₀_honest` is impossible** because they sum to different values. Actually, the sum check says `g₀(0) + g₀(1) = claimed_sum ≠ actual_sum = g₀_honest(0) + g₀_honest(1)`, so `g₀ ≠ g₀_honest`. Done — but we also need `(g₀ - g₀_honest).eval r₀ = 0` to propagate. If `(g₀ - g₀_honest).eval r₀ ≠ 0`, then `g₀(r₀) ≠ g₀_honest(r₀)`, meaning the claim for round 2 is wrong, and we apply the IH to rounds 1..n with the new wrong claim `g₀(r₀)` and the partially evaluated polynomial.

This inductive argument is the standard sumcheck soundness proof. The key insight: either the current round's challenge is a root of a nonzero degree-≤-1 polynomial, or the "wrong claim" propagates to the next round.

- [ ] **Step 5: Prove `sumcheck_soundness` (counting form)**

Strategy:
- From `sumcheck_soundness_det`, any accepting challenge vector has some `i` where `(rounds i).challenge` is a root of a nonzero degree-≤-1 polynomial.
- By `roots_le_one_of_deg_le_one`, at most 1 value in `S` is a root.
- Union bound: for each of `n` rounds, at most 1 bad value out of `|S|` choices, with the other `n-1` challenges free. Total bad tuples ≤ `n · 1 · |S|^(n-1)`.
- This uses `Finset.card_biUnion_le` or a direct counting argument.

- [ ] **Step 6: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 7: Commit**

```bash
git add LeanLongfellow/Sumcheck/Soundness.lean
git commit -m "feat(Sumcheck): prove sumcheck_soundness via Schwartz-Zippel"
```

---

### Task 9: Field Instantiation and Integration Test

**Files:**
- Create: `LeanLongfellow/Field/Basic.lean`

- [ ] **Step 1: Create `Field/Basic.lean` with ZMod instantiation and #eval tests**

```lean
import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Props
import Mathlib.Algebra.Field.ZMod

open Finset MultilinearPoly

/-! ## Instantiation for `ZMod p` (prime `p`)

Demonstrates that all definitions are computable over a concrete prime field.
Uses `ZMod 97` as a small example. -/

instance : Fact (Nat.Prime 97) := ⟨by decide⟩

/-- Example: 2-variable MLE over `ZMod 97`.
    Table: p(0,0) = 1, p(1,0) = 2, p(0,1) = 5, p(1,1) = 3.
    Extension: p(x,y) = 1·(1-x)(1-y) + 2·x(1-y) + 5·(1-x)·y + 3·x·y
              = 1 + x + 4y - 5xy -/
def examplePoly : MultilinearPoly (ZMod 97) 2 where
  table b :=
    match b 0, b 1 with
    | false, false => 1
    | true,  false => 2
    | false, true  => 5
    | true,  true  => 3

-- Sanity checks: table values recovered by eval at Boolean points
#eval examplePoly.eval (boolToField fun | 0 => false | 1 => false) -- expect 1
#eval examplePoly.eval (boolToField fun | 0 => true  | 1 => false) -- expect 2
#eval examplePoly.eval (boolToField fun | 0 => false | 1 => true)  -- expect 5
#eval examplePoly.eval (boolToField fun | 0 => true  | 1 => true)  -- expect 3

-- Extension evaluation: p(2, 3) = 1 + 2 + 12 - 30 = -15 = 82 (mod 97)
#eval examplePoly.eval (fun | 0 => 2 | 1 => 3) -- expect 82

-- Sum over hypercube: 1 + 2 + 5 + 3 = 11
#eval ∑ b : Fin 2 → Bool, examplePoly.table b -- expect 11

-- Partial evaluation: fix x₁ = 3, get 1-variable MLE
-- p(3, y) = 1 + 3 + 4y - 15y = 4 - 11y
-- p(3, 0) = 4, p(3, 1) = 4 - 11 = -7 = 90
#eval (examplePoly.partialEvalFirst 3).table (fun | 0 => false) -- expect 4
#eval (examplePoly.partialEvalFirst 3).table (fun | 0 => true)  -- expect 90

-- Honest prover polynomial for first round
-- sumFirstVar: c0 = p(0,0) + p(0,1) = 6, c1 = p(1,0) + p(1,1) = 5
-- g(X) = 6 + X*(5-6) = 6 - X
#eval (examplePoly.sumFirstVar).eval 0 -- expect 6
#eval (examplePoly.sumFirstVar).eval 1 -- expect 5
```

- [ ] **Step 2: Verify #eval outputs match expected values**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Expected: Build succeeds, #eval outputs match comments.

If `#eval` doesn't work due to computability issues with `Finset.sum`/`Finset.prod` over `Fin n → Bool`, use `#eval decide ...` or `native_decide` as a fallback. Another option is `Decidable` instances. If `#eval` is infeasible, replace with `example` proofs using `native_decide`:

```lean
example : examplePoly.eval (boolToField fun | 0 => false | 1 => false) = (1 : ZMod 97) := by
  native_decide
```

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Field/Basic.lean
git commit -m "feat(Field): add ZMod 97 instantiation with #eval integration tests"
```

---

### Task 10: Root Imports and Final Verification

**Files:**
- Modify: `LeanLongfellow.lean`
- Modify: `lakefile.lean` (if needed)

- [ ] **Step 1: Update root import file**

Replace `LeanLongfellow.lean` with:

```lean
import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Extension
import LeanLongfellow.MLE.Props
import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import LeanLongfellow.Sumcheck.Soundness
import LeanLongfellow.Field.Basic
```

- [ ] **Step 2: Full clean build**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake clean && lake build`
Expected: Build succeeds with no errors. Only acceptable warnings are from Mathlib internals.

- [ ] **Step 3: Verify no sorry remains**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && grep -r "sorry" LeanLongfellow/`
Expected: No matches (all proofs completed).

- [ ] **Step 4: Commit**

```bash
git add LeanLongfellow.lean
git commit -m "chore: add root imports, verify clean build with no sorry"
```

---

## Spec Coverage Checklist

| Spec Item | Task |
|-----------|------|
| `MultilinearPoly` type | Task 1 (table-based, improved from spec) |
| `MultilinearPoly.ofEvals` | Task 1 (trivially: `⟨f⟩` constructs from table) |
| `MultilinearPoly.eval` | Task 2 |
| `MultilinearPoly.partialEval` | Task 3 (`partialEvalFirst`) |
| `MultilinearPoly.restrict` | Task 3 (`sumFirstVar` — combines restriction + summation) |
| `mle_unique` | Task 4 |
| `mle_extension_exists` | Task 4 |
| `mle_degree_bound` | Task 5 (`sumFirstVar_natDegree_le`) |
| `mle_sum_hypercube` | Task 5 |
| `partial_eval_multilinear` | Task 3 (`partialEvalFirst_eval` — preserves eval semantics) |
| `SumcheckRound` / `SumcheckProtocol` | Task 6 |
| `sumcheck_completeness` | Task 7 |
| `sumcheck_soundness` | Task 8 |
| `sumcheck_round_reduce` | Task 7 (derived from `partialEval_table_sum`) |
| Schwartz-Zippel dependency | Task 8 (`roots_le_one_of_deg_le_one` via Mathlib) |
| Field instantiation (M5) | Task 9 (`ZMod 97`) |
| Testing (#eval) | Task 9 |

## Dependency Graph

```
Task 1 (Defs) → Task 2 (Eval) → Task 3 (PartialEval) → Task 4 (Extension)
                                       ↓                       ↓
                                  Task 5 (Props)          (independent)
                                       ↓
                                  Task 6 (Protocol) → Task 7 (Completeness) → Task 8 (Soundness)
                                                                                     ↓
                                                                               Task 9 (Field)
                                                                                     ↓
                                                                               Task 10 (Root)
```

Tasks 4 and 5 are independent of each other (both depend on Tasks 2-3).
Task 9 can start after Task 5 (doesn't need soundness proofs).
