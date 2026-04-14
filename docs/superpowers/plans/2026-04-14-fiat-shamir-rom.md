# Fiat-Shamir ROM Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the Fiat-Shamir transform of the sumcheck protocol is sound in the Random Oracle Model with concrete bound `n / |F|`.

**Architecture:** Minimal probabilistic layer using finite counting (no monads, no VCVio). Per-round oracle model where each round has an independent oracle. The non-interactive protocol wraps the existing interactive `verifierAccepts`. Soundness reduces to `sumcheck_soundness_det` plus a union bound over uniform oracle outputs.

**Tech Stack:** Lean 4 v4.30.0-rc1, Mathlib4 (for `Fintype`, `Finset.card`, `Rat`)

---

## File Structure

```
LeanLongfellow/
├── FiatShamir/
│   ├── Oracle.lean        # SumcheckOracle type, oracleProb, uniform distribution lemmas
│   ├── Transform.lean     # FiatShamirProof, deriveChallenges, toRounds, fsVerifierAccepts
│   └── Soundness.lean     # fiatShamir_soundness theorem
```

## Existing APIs Used (DO NOT MODIFY)

From `Sumcheck/Protocol.lean`:
- `SumcheckRound F` — structure with `prover_poly : F[X]` and `challenge : F`
- `verifierAccepts (p : MultilinearPoly F n) (claimed_sum : F) (rounds : Fin n → SumcheckRound F) : Prop`
- `honestProver : MultilinearPoly F n → (Fin n → F) → Fin n → SumcheckRound F`

From `Sumcheck/Completeness.lean`:
- `sumcheck_completeness (p : MultilinearPoly F n) (challenges : Fin n → F) : verifierAccepts p (∑ b, p.table b) (honestProver p challenges)`

From `Sumcheck/Soundness.lean`:
- `sumcheck_soundness_det (p : MultilinearPoly F n) (claimed_sum : F) (rounds : Fin n → SumcheckRound F) (hn : 0 < n) (hclaim : claimed_sum ≠ ∑ b, p.table b) (haccept : verifierAccepts p claimed_sum rounds) (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1) : ∃ i, ∃ diff, diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧ diff.eval (rounds i).challenge = 0`
  - Note: requires `[DecidableEq F]` in scope.
- `roots_le_one_of_deg_le_one {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1) (S : Finset F) : (S.filter (fun r => p.eval r = 0)).card ≤ 1`

From `MLE/Props.lean`:
- `sumFirstVar_natDegree_le (p : MultilinearPoly F (n + 1)) : (sumFirstVar p).natDegree ≤ 1`

---

### Task 1: Random Oracle Type and Basic Properties

**Files:**
- Create: `LeanLongfellow/FiatShamir/Oracle.lean`

- [ ] **Step 1: Create `Oracle.lean` with the oracle type and probability definition**

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.Order.Field.Basic

/-! # Random Oracle Model for Sumcheck Fiat-Shamir

Minimal probability infrastructure for ROM soundness.
A random oracle is a function `Fin n → F[X] → F`, one per sumcheck round.
Probability is defined as counting over the finite set of all such functions. -/

open Finset

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- A random oracle for the sumcheck Fiat-Shamir transform.
    At round `i`, given the prover's polynomial, returns a challenge in `F`. -/
def SumcheckOracle (F : Type*) (n : ℕ) := Fin n → Polynomial F → F

/-- All oracle functions form a finite type when `F` is finite.
    Note: `Polynomial F` is infinite, so `SumcheckOracle F n` is technically infinite.
    We restrict to oracles that are determined by their values on a finite set of inputs. -/

-- IMPORTANT: Polynomial F is NOT finite, so Fin n → Polynomial F → F is NOT a Fintype.
-- We need a different approach. See Step 2.
```

**STOP.** There's a fundamental issue: `Polynomial F` is infinite (unbounded degree), so `Polynomial F → F` has no `Fintype` instance, and we can't count over all oracles.

**Resolution:** Restrict the oracle domain. The adversary's proof contains `n` polynomials, and the oracle is only evaluated on those specific polynomials. So we model the oracle as `Fin n → F` — a random challenge per round, independent of the prover's polynomial. This is equivalent in the ROM for our non-adaptive setting: the adversary commits to round polynomials, and the oracle output is uniform regardless of input.

Replace the above with:

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Order.Basic

/-! # Random Oracle Model for Sumcheck Fiat-Shamir

Minimal probability infrastructure for ROM soundness.

Since the adversary produces a fixed proof (n polynomials) and the oracle
is evaluated once per round, we model the oracle as `Fin n → F`: a
random challenge per round. This is equivalent to the full ROM for our
non-adaptive adversary model — the oracle output is uniform regardless
of input, so only the output matters. -/

open Finset

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- Random challenges: one uniformly random field element per round. -/
abbrev RandomChallenges (F : Type*) (n : ℕ) := Fin n → F

noncomputable instance (F : Type*) [Fintype F] (n : ℕ) : Fintype (RandomChallenges F n) :=
  Pi.fintype

/-- The number of oracle/challenge assignments. -/
theorem card_randomChallenges (F : Type*) [Fintype F] (n : ℕ) :
    Fintype.card (RandomChallenges F n) = Fintype.card F ^ n := by
  exact Fintype.card_fun

/-- Count how many challenge assignments satisfy a predicate. -/
noncomputable def countSat {n : ℕ} (P : RandomChallenges F n → Prop) [DecidablePred P] : ℕ :=
  (Finset.univ.filter P).card

/-- The probability bound: countSat P / |F|^n ≤ bound.
    We state bounds as `countSat P ≤ bound * |F|^(n-1)` (multiply through)
    to stay in ℕ and avoid rational arithmetic. -/

/-- For a fixed value `v : F`, the number of challenge vectors where
    the i-th challenge equals `v` is `|F|^(n-1)`. -/
theorem countSat_eq_val {n : ℕ} (i : Fin n) (v : F) :
    countSat (fun cs : RandomChallenges F n => cs i = v) = Fintype.card F ^ (n - 1) := by
  sorry -- proved in Step 3
```

- [ ] **Step 2: Verify stub compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `countSat_eq_val`**

Strategy:
- The set `{cs : Fin n → F | cs i = v}` is isomorphic to `(Fin (n-1) → F)` — all other coordinates are free, and coordinate `i` is fixed to `v`.
- Use `Fintype.card_pi` and a bijection that inserts `v` at position `i`.
- Alternatively: `Finset.filter` on `Finset.univ` for `Fin n → F`, fixing coordinate `i`, and count using `Finset.card_filter_piFinset_eq` or manual counting.
- The bijection approach: `{cs | cs i = v} ≃ (∀ j : {j // j ≠ i}, F)`. The target has `Fintype.card F ^ (n - 1)` elements since `{j // j ≠ i}` has `n - 1` elements.

- [ ] **Step 4: Add the union bound lemma**

```lean
/-- Union bound: if each of `n` events has at most `k` bad challenges out of `|F|^n`,
    then the union has at most `n * k` bad challenges. -/
theorem countSat_union_bound {n : ℕ} {m : ℕ}
    (P : Fin m → RandomChallenges F n → Prop)
    [∀ j, DecidablePred (P j)]
    (hbound : ∀ j, countSat (P j) ≤ k) :
    countSat (fun cs => ∃ j, P j cs) ≤ m * k := by
  sorry -- proved in Step 5
```

- [ ] **Step 5: Prove `countSat_union_bound`**

Strategy:
- `{cs | ∃ j, P j cs} ⊆ ⋃ j, {cs | P j cs}`
- `|⋃ j, Sⱼ| ≤ ∑ j, |Sⱼ|` by `Finset.card_biUnion_le`
- `∑ j, |Sⱼ| ≤ ∑ j, k = m * k`

- [ ] **Step 6: Add the key lemma — random challenge hits a root**

```lean
/-- For a fixed nonzero polynomial `d` of degree ≤ 1, the number of
    challenge vectors where `d.eval (cs i) = 0` is at most `|F|^(n-1)`. -/
theorem countSat_root_hit {n : ℕ} (i : Fin n)
    {d : F[X]} (hd : d ≠ 0) (hdeg : d.natDegree ≤ 1) :
    countSat (fun cs : RandomChallenges F n => d.eval (cs i) = 0) ≤
      Fintype.card F ^ (n - 1) := by
  sorry -- proved in Step 7
```

- [ ] **Step 7: Prove `countSat_root_hit`**

Strategy:
- The set `{cs | d.eval (cs i) = 0}` ⊆ `{cs | cs i ∈ roots(d)}`.
- `d` has at most 1 root (degree ≤ 1, nonzero), so `cs i` is constrained to at most 1 value.
- For each such value `v`, `countSat (cs i = v) = |F|^(n-1)` by `countSat_eq_val`.
- If there are 0 roots: the set is empty, count = 0 ≤ |F|^(n-1).
- If there is 1 root `v`: the set ⊆ `{cs | cs i = v}`, count ≤ |F|^(n-1).
- Use `roots_le_one_of_deg_le_one` or `Polynomial.card_roots'` for the root count.

- [ ] **Step 8: Verify all proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 9: Commit**

```bash
git add LeanLongfellow/FiatShamir/Oracle.lean
git commit -m "feat(FiatShamir): add random oracle type, countSat, union bound, root hit lemma"
```

---

### Task 2: Non-Interactive Protocol Definitions

**Files:**
- Create: `LeanLongfellow/FiatShamir/Transform.lean`

- [ ] **Step 1: Create `Transform.lean` with protocol definitions**

```lean
import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import LeanLongfellow.FiatShamir.Oracle

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}

/-- A non-interactive sumcheck proof: the round polynomials.
    Challenges are derived from the random oracle (modeled as RandomChallenges). -/
structure FiatShamirProof (F : Type*) [Field F] (n : ℕ) where
  round_polys : Fin n → Polynomial F

/-- Reconstruct interactive rounds from a proof and random challenges. -/
def toRounds (proof : FiatShamirProof F n) (cs : RandomChallenges F n) :
    Fin n → SumcheckRound F :=
  fun i => ⟨proof.round_polys i, cs i⟩

/-- The non-interactive verifier: given a proof and challenges (from oracle),
    run the interactive verifier. -/
def fsVerifierAccepts (p : MultilinearPoly F n) (claimed_sum : F)
    (proof : FiatShamirProof F n) (cs : RandomChallenges F n) : Prop :=
  verifierAccepts p claimed_sum (toRounds proof cs)

/-- `fsVerifierAccepts` is exactly `verifierAccepts` with reconstructed rounds. -/
theorem fsVerifierAccepts_iff (p : MultilinearPoly F n) (claimed_sum : F)
    (proof : FiatShamirProof F n) (cs : RandomChallenges F n) :
    fsVerifierAccepts p claimed_sum proof cs ↔
      verifierAccepts p claimed_sum (toRounds proof cs) := by
  rfl

/-- Extract a FiatShamirProof from the honest interactive prover. -/
noncomputable def fsHonestProof (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    FiatShamirProof F n where
  round_polys i := (honestProver p cs i).prover_poly

/-- The honest FS proof, when combined with the same challenges,
    reconstructs the honest interactive prover's rounds. -/
theorem toRounds_fsHonest (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    toRounds (fsHonestProof p cs) cs = honestProver p cs := by
  sorry -- proved in Step 3
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `toRounds_fsHonest`**

Strategy:
- `toRounds (fsHonestProof p cs) cs i = ⟨(honestProver p cs i).prover_poly, cs i⟩`
- `honestProver p cs i = ⟨(honestProver p cs i).prover_poly, (honestProver p cs i).challenge⟩`
- Need `(honestProver p cs i).challenge = cs i`. This follows from the definition of `honestProver`: the challenge at round `i` is `challenges i = cs i`.
- Use `funext` + `SumcheckRound.ext` (or `Prod.ext`).

Key insight: `honestProver` stores `challenges i` as the challenge. From the definition, for `n + 1`:
- Round 0: `⟨sumFirstVar p, challenges 0⟩` → challenge = `cs 0` ✓
- Round j.succ: recursive, but challenge comes from `(fun k => challenges k.succ) j` which traces back to `cs (j.succ)` ✓

Prove by induction on `n`, using `honestProver_zero` and `honestProver_succ`.

- [ ] **Step 4: Prove FS completeness**

```lean
/-- Fiat-Shamir completeness: the honest FS prover is always accepted. -/
theorem fiatShamir_completeness (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    fsVerifierAccepts p (∑ b : Fin n → Bool, p.table b) (fsHonestProof p cs) cs := by
  unfold fsVerifierAccepts
  rw [toRounds_fsHonest]
  exact sumcheck_completeness p cs
```

- [ ] **Step 5: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 6: Commit**

```bash
git add LeanLongfellow/FiatShamir/Transform.lean
git commit -m "feat(FiatShamir): add non-interactive protocol, prove FS completeness"
```

---

### Task 3: ROM Soundness

**Files:**
- Create: `LeanLongfellow/FiatShamir/Soundness.lean`

- [ ] **Step 1: Create `Soundness.lean` with the main theorem stub**

```lean
import LeanLongfellow.FiatShamir.Oracle
import LeanLongfellow.FiatShamir.Transform
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **Fiat-Shamir ROM Soundness.**

For any adversary (a function from random challenges to a proof),
if the claimed sum is wrong, the number of challenge vectors that
make the verifier accept is at most `n * |F|^(n-1)`.

Dividing by `|F|^n` gives the probability bound `n / |F|`. -/
theorem fiatShamir_soundness {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ 1) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * Fintype.card F ^ (n - 1) := by
  sorry
```

- [ ] **Step 2: Verify stub compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove `fiatShamir_soundness`**

Strategy — this is the main proof, connecting all the pieces:

1. **Unfold to interactive soundness.** For any `cs` in the bad set, `verifierAccepts p claimed_sum (toRounds (adversary cs) cs)` holds. By `sumcheck_soundness_det` (with `hn`, `hclaim`, and `hdeg`), there exists `i : Fin n` and nonzero `diff` with degree ≤ 1 such that `diff.eval (cs i) = 0`.

2. **Decompose by witness round.** The bad set ⊆ `⋃ i : Fin n, {cs | ∃ diff, diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧ diff.eval (cs i) = 0}`.

3. **Bound each round.** For fixed `i`, the set `{cs | ∃ diff, ... ∧ diff.eval (cs i) = 0}` ⊆ `{cs | cs i ∈ S}` where `S` is the set of roots of all possible `diff` polynomials. But more directly: the `diff` depends on `adversary cs` which depends on `cs`. The key insight is that `diff.eval (cs i) = 0` means `cs i` is a root of a degree-≤-1 polynomial. Regardless of which `diff` it is, there are at most 1 possible values of `cs i` that work (by `roots_le_one_of_deg_le_one`). So fixing `cs i` to any root value, the other `n-1` coordinates are free: at most `1 * |F|^(n-1)` = `|F|^(n-1)` bad vectors per round.

   Actually this step needs care because `diff` depends on `cs`. The clean approach:

   For each fixed `i : Fin n`, define `Pᵢ(cs) := ∃ diff, diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧ diff.eval (cs i) = 0`. We need `countSat Pᵢ ≤ |F|^(n-1)`.

   `Pᵢ(cs)` says `cs i` is a root of SOME nonzero degree-≤-1 polynomial. A degree-≤-1 polynomial has at most 1 root. But different `cs` might have different `diff`'s.

   However: `Pᵢ(cs)` implies there exist `a, b : F` with `(a, b) ≠ (0, 0)` such that `a + b * (cs i) = 0`, i.e., `cs i = -a/b` (if b ≠ 0) or `a = 0` (contradiction). So `cs i` is determined (at most 1 value works for each `diff`, but different `diff`'s give different values).

   Alternative cleaner bound: For fixed `cs` with other coordinates fixed, varying only `cs i` over all of `F`, at most 1 value of `cs i` can satisfy `diff.eval (cs i) = 0` for ANY nonzero degree-≤-1 `diff`. So `|{cs | Pᵢ(cs)}| ≤ |F|^(n-1)`. But this isn't quite right either because `diff` depends on `cs i` too (via `adversary cs`).

   **Correct approach for the formalization:** Don't decompose by round. Instead, directly use:
   
   The bad set = `{cs | fsVerifierAccepts p claimed_sum (adversary cs) cs}`.
   
   For each `cs` in this set, `sumcheck_soundness_det` gives `i` and `diff` with `diff.eval (cs i) = 0` and `diff ≠ 0` and `diff.natDegree ≤ 1`.
   
   Define `Bᵢ = {cs | the witness from sumcheck_soundness_det for cs has index i AND diff.eval (cs i) = 0}`.
   
   Bad set ⊆ `⋃ᵢ Bᵢ`. For each `Bᵢ`, every `cs ∈ Bᵢ` satisfies: there exists a nonzero degree-≤-1 poly whose eval at `cs i` is 0. Use `countSat_root_hit` to bound `|Bᵢ| ≤ |F|^(n-1)`.
   
   Wait, `countSat_root_hit` needs a FIXED `diff`. But `diff` varies with `cs`.
   
   **Simplest correct approach:** For each `cs` in the bad set, SOME `cs i` is a root of a nonzero degree-≤-1 polynomial. That polynomial has at most 1 root in `F`. So `cs i` takes at most 1 value. For that fixed value of `cs i`, the other `n-1` coordinates are free: `|F|^(n-1)` possibilities. Union over `n` choices of `i`: `n * |F|^(n-1)`.
   
   But "that polynomial" depends on `cs`! This is the subtle point.
   
   **Actually correct approach:** The cleanest way is:
   
   `|bad set| ≤ |{cs | ∃ i, ∃ v ∈ roots_of_some_deg1_poly, cs i = v}|`
   `≤ ∑ᵢ |{cs | cs i ∈ ⋃_{deg≤1 polys} roots(poly)}|`
   
   But this overcounts because "⋃ roots" could be all of F.
   
   **The standard ROM argument works differently.** The point is that in the ROM, the challenges are INDEPENDENT and UNIFORM. So:
   
   `Pr[bad] = Pr[∃ i, diff_i.eval(cs i) = 0]`
   `≤ ∑ᵢ Pr[diff_i.eval(cs i) = 0]`    (union bound)
   
   For each `i`: `diff_i` may depend on `cs`, but `cs i` is uniform in F and independent of `diff_i`'s dependence on other coordinates. Wait, is it? `diff_i` comes from `sumcheck_soundness_det` applied to `toRounds (adversary cs) cs`. The adversary's proof and the diff both depend on ALL of `cs`, including `cs i`.
   
   **This is the core subtlety of Fiat-Shamir soundness.** The standard proof handles it by arguing that even though `diff` depends on `cs`, for a FIXED adversary and FIXED values of all OTHER challenges, varying `cs i` uniformly still gives at most probability 1/|F| of hitting the root.
   
   For the formalization, this means: fix all coordinates except `i`, and count over `cs i`. For each fixed "context" (other coordinates), the adversary determines a specific `diff` (which may depend on `cs i` through the adversary!). But actually — in our model, the adversary IS the proof itself. The adversary's round polynomials `(adversary cs).round_polys` depend on ALL of cs. So `diff` can depend on `cs i`.
   
   **This breaks the simple counting argument.** The fix: we need the adversary to be "non-adaptive at round i" — i.e., the proof polynomial at round i doesn't depend on `cs i`. This is actually guaranteed by the structure of Fiat-Shamir: the round-i polynomial is computed BEFORE seeing challenge i.
   
   **For our formalization:** We need an additional hypothesis or structural constraint:
   
   ```lean
   -- The adversary's round-i polynomial depends only on challenges 0..i-1
   (h_nonadaptive : ∀ cs cs' : RandomChallenges F n, ∀ i : Fin n,
     (∀ j : Fin n, j < i → cs j = cs' j) →
     (adversary cs).round_polys i = (adversary cs').round_polys i)
   ```
   
   With this, fix challenges 0..i-1. The adversary's round-i polynomial is fixed. `diff` at round i is fixed. Then `cs i` is uniform, and `Pr[diff.eval(cs i) = 0] ≤ 1/|F|`.
   
   **Add this hypothesis to the theorem statement.**

Here is the corrected theorem:

```lean
/-- **Fiat-Shamir ROM Soundness.**

For any non-adaptive adversary (round-i polynomial depends only on
challenges 0..i-1), if the claimed sum is wrong, the number of
challenge vectors that fool the verifier is at most `n * |F|^(n-1)`.

The non-adaptive constraint models the real Fiat-Shamir transform:
the prover computes round i before seeing challenge i. -/
theorem fiatShamir_soundness {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ 1)
    -- Non-adaptive: round i's polynomial depends only on challenges 0..i-1
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * Fintype.card F ^ (n - 1) := by
  sorry
```

The proof proceeds:
1. For `cs` in the bad set, `sumcheck_soundness_det` gives witness `(i, diff)`.
2. By `h_nonadaptive`, `(adversary cs).round_polys i` depends only on `cs 0, ..., cs (i-1)`. The honest round-i polynomial (from the partial evaluation) also depends only on `cs 0, ..., cs (i-1)`. So `diff = (adversary cs).round_polys i - honest_round_i_poly` depends only on `cs 0, ..., cs (i-1)`.
3. `diff.eval (cs i) = 0` where `diff` is independent of `cs i`. By `countSat_root_hit`-style reasoning (fixing all coords except `i`), at most 1 value of `cs i` works.
4. Counting: for each `i`, at most `|F|^(n-1)` bad vectors. Union over `n` rounds: `n * |F|^(n-1)`.

   For the counting argument, decompose `{cs | bad}` by the first round `i` where `diff.eval(cs i) = 0`. Define:
   
   `Bᵢ = {cs | verifier accepts ∧ i is the minimal witness index from soundness_det}`
   
   Or simpler: just bound the union.
   
   `{cs | bad} ⊆ ⋃ᵢ {cs | ∃ diff, diff ≠ 0 ∧ deg ≤ 1 ∧ diff depends only on cs<i ∧ diff.eval(cs i) = 0}`
   
   For fixed `i`, split the sum over `cs` as: outer sum over `(cs 0, ..., cs (i-1), cs (i+1), ..., cs (n-1))` (which determines `diff`), inner sum over `cs i`. For each outer assignment, `diff` is fixed and nonzero with degree ≤ 1, so at most 1 value of `cs i` satisfies `diff.eval(cs i) = 0`. Inner count ≤ 1. Outer count = `|F|^(n-1)`. Total for round `i`: ≤ `|F|^(n-1)`.

   In Lean, this decomposition uses `Fintype.sum_prod_type` or a fiber-counting argument. The key lemma needed is a "fiber bound":
   
   ```lean
   /-- If for each value of the "other" coordinates, at most `k` values of
       coordinate `i` satisfy `P`, then `countSat P ≤ k * |F|^(n-1)`. -/
   theorem countSat_fiber_bound (i : Fin n)
       (P : RandomChallenges F n → Prop) [DecidablePred P]
       (hfiber : ∀ others : ∀ j : {j : Fin n // j ≠ i}, F,
         (Finset.univ.filter (fun v : F => P (insertAt i v others))).card ≤ k) :
       countSat P ≤ k * Fintype.card F ^ (n - 1)
   ```
   
   where `insertAt i v others` reconstructs the full challenge vector. This lemma may be the hardest part to formalize cleanly due to the type juggling with `{j // j ≠ i}`.

- [ ] **Step 4: Prove helper lemmas and `fiatShamir_soundness`**

Try to prove the theorem. If the fiber decomposition is too hard in Lean, use `sorry` for the counting step and report DONE_WITH_CONCERNS.

- [ ] **Step 5: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 6: Commit**

```bash
git add LeanLongfellow/FiatShamir/Soundness.lean
git commit -m "feat(FiatShamir): prove ROM soundness for sumcheck Fiat-Shamir"
```

---

### Task 4: Root Imports and Final Verification

**Files:**
- Modify: `LeanLongfellow.lean`

- [ ] **Step 1: Update root imports**

Add to `LeanLongfellow.lean`:

```lean
import LeanLongfellow.FiatShamir.Oracle
import LeanLongfellow.FiatShamir.Transform
import LeanLongfellow.FiatShamir.Soundness
```

- [ ] **Step 2: Full build**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Check sorry count**

Run: `grep -rn "sorry" LeanLongfellow/FiatShamir/`

- [ ] **Step 4: Commit**

```bash
git add LeanLongfellow.lean
git commit -m "chore: add FiatShamir imports to root module"
```

---

## Spec Coverage Checklist

| Spec Item | Task |
|-----------|------|
| `SumcheckOracle` / `RandomChallenges` type | Task 1 |
| `oracleProb` / `countSat` | Task 1 |
| `uniform_hit_prob` / `countSat_eq_val` | Task 1 |
| `uniform_root_prob` / `countSat_root_hit` | Task 1 |
| `oracle_union_bound` / `countSat_union_bound` | Task 1 |
| `FiatShamirProof` | Task 2 |
| `deriveChallenges` / `toRounds` | Task 2 |
| `fsVerifierAccepts` | Task 2 |
| `fsVerifier_iff` / `fsVerifierAccepts_iff` | Task 2 |
| `fsHonest_accepted` / `fiatShamir_completeness` | Task 2 |
| `fiatShamir_soundness` | Task 3 |

## Design Change from Spec

The spec modeled the oracle as `Fin n → Polynomial F → F`. This is infinite (Polynomial F is unbounded), so `Fintype` doesn't apply and we can't count. The plan uses `RandomChallenges F n = Fin n → F` instead — a random challenge per round, with a non-adaptivity hypothesis on the adversary. This is equivalent for non-adaptive adversaries and avoids infinite type issues.

## Dependency Graph

```
Task 1 (Oracle) → Task 2 (Transform) → Task 3 (Soundness) → Task 4 (Root)
```

Strictly sequential — each task imports the previous.
