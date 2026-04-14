# Abstract Ligero + End-to-End Longfellow Soundness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove end-to-end Longfellow soundness: if the abstract Ligero binding property holds, the verifier never accepts a wrong claim.

**Architecture:** Constraint types (linear + quadratic) with satisfaction predicates. `LigeroScheme` typeclass with commit/verify/binding. Witness encoding maps sumcheck transcript to a vector. Constraint generation produces linear/quadratic constraints whose satisfaction implies the sumcheck claim is correct. End-to-end theorem chains: Ligero binding → constraint satisfaction → claim correctness.

**Tech Stack:** Lean 4 v4.30.0-rc1, Mathlib4, existing MLE/Sumcheck modules

---

## File Structure

```
LeanLongfellow/
├── Ligero/
│   ├── Constraints.lean   # LinearConstraints, QuadConstraint, satisfaction predicates
│   ├── Interface.lean     # LigeroScheme typeclass
│   ├── Generate.lean      # Witness encoding, constraint generation, bridge theorem
│   └── Longfellow.lean    # longfellowVerifierAccepts, soundness theorems
```

## Existing APIs (DO NOT MODIFY)

| API | Signature |
|-----|-----------|
| `MultilinearPoly F n` | `structure { table : (Fin n → Bool) → F }` |
| `MultilinearPoly.eval` | `(p : MultilinearPoly F n) → (Fin n → F) → F` |
| `eval_boolVec` | `p.eval (boolToField b) = p.table b` |
| `mle_unique` | same table → same eval everywhere |
| `verifierAccepts` | `MultilinearPoly F n → F → (Fin n → SumcheckRound F) → Prop` |
| `SumcheckRound F` | `{ prover_poly : F[X], challenge : F }` |
| `sumcheck_completeness` | honest prover → verifier accepts |
| `sumcheck_soundness_det` | wrong claim + accept → ∃ root hit |

---

### Task 1: Constraint Types

**Files:**
- Create: `LeanLongfellow/Ligero/Constraints.lean`

- [ ] **Step 1: Create `Constraints.lean` with types and satisfaction predicates**

```lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs

open Finset

/-! # Linear and Quadratic Constraints

Longfellow generates linear and quadratic constraints from the padded
sumcheck transcript. Ligero proves these constraints hold on a committed
witness. -/

variable {F : Type*} [Field F]

/-- A system of linear constraints: A · w = b.
    `m` constraints over a witness of size `n`. -/
structure LinearConstraints (F : Type*) [Field F] (m n : ℕ) where
  /-- Coefficient matrix -/
  matrix : Fin m → Fin n → F
  /-- Target vector -/
  target : Fin m → F

/-- A single quadratic constraint: w[left] · w[right] = w[output]. -/
structure QuadConstraint (n : ℕ) where
  left : Fin n
  right : Fin n
  output : Fin n

/-- A witness satisfies the linear constraints. -/
def satisfiesLinear {m n : ℕ} (w : Fin n → F) (lc : LinearConstraints F m n) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, lc.matrix i j * w j = lc.target i

/-- A witness satisfies a quadratic constraint. -/
def satisfiesQuad {n : ℕ} (w : Fin n → F) (qc : QuadConstraint n) : Prop :=
  w qc.left * w qc.right = w qc.output

/-- A witness satisfies all linear and quadratic constraints. -/
def satisfiesAll {m n q : ℕ} (w : Fin n → F)
    (lcs : LinearConstraints F m n) (qcs : Fin q → QuadConstraint n) : Prop :=
  satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i)

/-- satisfiesAll unfolds to its components. -/
theorem satisfiesAll_iff {m n q : ℕ} (w : Fin n → F)
    (lcs : LinearConstraints F m n) (qcs : Fin q → QuadConstraint n) :
    satisfiesAll w lcs qcs ↔ satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i) :=
  Iff.rfl
```

- [ ] **Step 2: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Ligero/Constraints.lean
git commit -m "feat(Ligero): add linear/quadratic constraint types and satisfaction predicates"
```

---

### Task 2: Abstract Ligero Interface

**Files:**
- Create: `LeanLongfellow/Ligero/Interface.lean`

- [ ] **Step 1: Create `Interface.lean` with the LigeroScheme typeclass**

```lean
import LeanLongfellow.Ligero.Constraints

/-! # Abstract Ligero Commitment Scheme

Ligero is modeled as a typeclass with three components:
- `commit`: produce a commitment from a witness
- `verify`: check a proof against a commitment and constraints
- `binding`: if verify accepts on a committed witness, the witness satisfies the constraints

This abstracts Ligero's internals (Reed-Solomon, Merkle trees, proximity testing)
into a single binding property. The internals can be formalized separately. -/

variable {F : Type*} [Field F]

/-- Abstract Ligero commitment scheme.
    Parameterized by field `F` and dimensions `n` (witness size),
    `m` (number of linear constraints), `q` (number of quadratic constraints). -/
class LigeroScheme (F : Type*) [Field F] (n m q : ℕ) where
  /-- Commitment type (e.g., Merkle root in a concrete instantiation) -/
  Commitment : Type
  /-- Proof type (e.g., column openings + Merkle paths) -/
  Proof : Type
  /-- Produce a commitment from a witness vector -/
  commit : (Fin n → F) → Commitment
  /-- Verify a proof against a commitment and constraints -/
  verify : Commitment → LinearConstraints F m n →
           (Fin q → QuadConstraint n) → Proof → Prop
  /-- **Binding axiom:** if verify accepts on a commitment to witness `w`,
      then `w` satisfies all the constraints.
      This is the key security property — it abstracts Ligero's
      low-degree test, linear constraint test, and quadratic constraint test. -/
  binding : ∀ (w : Fin n → F) (lcs : LinearConstraints F m n)
              (qcs : Fin q → QuadConstraint n) (π : Proof),
    verify (commit w) lcs qcs π → satisfiesAll w lcs qcs
```

- [ ] **Step 2: Verify it compiles**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/Ligero/Interface.lean
git commit -m "feat(Ligero): add abstract LigeroScheme typeclass with binding axiom"
```

---

### Task 3: Constraint Generation and Bridge Theorem

**Files:**
- Create: `LeanLongfellow/Ligero/Generate.lean`

This is the most substantial task. It defines how a sumcheck transcript is encoded as a witness vector, generates constraints, and proves the bridge theorem.

- [ ] **Step 1: Create `Generate.lean` with witness encoding and constraint generation**

The key design decision: how to encode the sumcheck transcript as a witness vector.

**Witness encoding for an n-round sumcheck:**
- The witness stores the polynomial evaluations at 0 and 1 for each round.
- Position `2*i` = `round_i.prover_poly.eval 0`
- Position `2*i + 1` = `round_i.prover_poly.eval 1`
- Witness size = `2 * n`

The linear constraints encode the telescoping sum-check conditions:
- Constraint 0: `w[0] + w[1] = claimed_sum` (round 0 sums to claim)
- Constraint i (for i > 0): `w[2*i] + w[2*i+1] = round_{i-1}_poly.eval(challenge_{i-1})`

But wait — `round_{i-1}_poly.eval(challenge_{i-1})` depends on the polynomial, not just the witness entries at 0 and 1. For a degree-≤-1 polynomial, `p.eval(r) = p.eval(0) + r * (p.eval(1) - p.eval(0))` = `(1-r) * p.eval(0) + r * p.eval(1)` = `(1-r) * w[2*(i-1)] + r * w[2*(i-1)+1]`.

So the constraint is:
- `w[2*i] + w[2*i+1] = (1 - r_{i-1}) * w[2*(i-1)] + r_{i-1} * w[2*(i-1)+1]`

This is a LINEAR constraint on the witness! The challenges `r_i` are public (from Fiat-Shamir), so they're constants in the constraint matrix.

```lean
import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F]

/-! # Constraint Generation from Sumcheck Transcript

The padded sumcheck transcript is encoded as a witness vector of polynomial
evaluations. Linear constraints encode the telescoping sum-check conditions.
For a degree-≤-1 polynomial: `p(r) = (1-r)·p(0) + r·p(1)`, so all
constraints are linear in the witness entries. -/

/-- Witness size for an n-round sumcheck: 2 entries per round
    (polynomial evaluated at 0 and 1). -/
def witnessSize (n : ℕ) : ℕ := 2 * n

/-- Encode a sumcheck transcript as a witness vector.
    Position 2i = round_i.prover_poly.eval 0
    Position 2i+1 = round_i.prover_poly.eval 1 -/
noncomputable def encodeWitness {n : ℕ} (rounds : Fin n → SumcheckRound F) :
    Fin (witnessSize n) → F :=
  fun k =>
    let i : Fin n := ⟨k.val / 2, by omega⟩
    if k.val % 2 = 0
    then (rounds i).prover_poly.eval 0
    else (rounds i).prover_poly.eval 1

/-- The number of linear constraints: n (one per round).
    Constraint i says: w[2i] + w[2i+1] = target_i
    where target_0 = claimed_sum
    and target_i = (1-r_{i-1}) * w[2(i-1)] + r_{i-1} * w[2(i-1)+1] for i > 0. -/

/-- Generate the linear constraint matrix and target for the sumcheck.
    This encodes the telescoping: at each round, the polynomial's
    sum (eval at 0 + eval at 1) must equal the previous round's eval at the challenge. -/
noncomputable def generateConstraints {n : ℕ} (claimed_sum : F)
    (challenges : Fin n → F) : LinearConstraints F n (witnessSize n) where
  matrix i j :=
    -- Row i encodes: w[2i] + w[2i+1] - ((1-r_{i-1})*w[2(i-1)] + r_{i-1}*w[2(i-1)+1]) = 0
    -- Rearranged: w[2i] + w[2i+1] = target_i
    -- As matrix row: coefficient of w[j]
    if j.val = 2 * i.val then 1          -- w[2i] coefficient
    else if j.val = 2 * i.val + 1 then 1 -- w[2i+1] coefficient
    else if (i : ℕ) > 0 ∧ j.val = 2 * (i.val - 1) then
      -(1 - challenges ⟨i.val - 1, by omega⟩)  -- w[2(i-1)] coefficient
    else if (i : ℕ) > 0 ∧ j.val = 2 * (i.val - 1) + 1 then
      -(challenges ⟨i.val - 1, by omega⟩)       -- w[2(i-1)+1] coefficient
    else 0
  target i :=
    if (i : ℕ) = 0 then claimed_sum else 0

/-- The final evaluation constraint: the last round polynomial evaluated
    at the last challenge must equal p.eval(challenges).
    This is a single linear constraint (since deg ≤ 1):
    (1-r_{n-1}) * w[2(n-1)] + r_{n-1} * w[2(n-1)+1] = p.eval(challenges) -/
noncomputable def generateFinalConstraint {n : ℕ}
    (p : MultilinearPoly F n) (challenges : Fin n → F) :
    LinearConstraints F 1 (witnessSize n) where
  matrix _ j :=
    if hn : 0 < n then
      let last := n - 1
      if j.val = 2 * last then (1 - challenges ⟨last, by omega⟩)
      else if j.val = 2 * last + 1 then challenges ⟨last, by omega⟩
      else 0
    else 0
  target _ := p.eval challenges
```

- [ ] **Step 2: Verify stubs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 3: Prove the bridge theorem**

```lean
/-- **Bridge theorem:** if the witness (encoded from a transcript) satisfies
    the generated linear constraints, then the sumcheck verifier's
    sum-check conditions hold.
    
    This connects Ligero's constraint satisfaction to sumcheck acceptance. -/
theorem constraints_encode_sumcheck {n : ℕ}
    (claimed_sum : F) (challenges : Fin n → F)
    (rounds : Fin n → SumcheckRound F)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_challenges : ∀ i, (rounds i).challenge = challenges i)
    (w : Fin (witnessSize n) → F)
    (hw : w = encodeWitness rounds)
    (h_sat : satisfiesLinear w (generateConstraints claimed_sum challenges))
    (h_final : satisfiesLinear w (generateFinalConstraint p challenges)) :
    verifierAccepts p claimed_sum rounds := by
  sorry -- see proof strategy below
```

**Proof strategy:**

`verifierAccepts` has two conjuncts:

**Conjunct 1 (sum checks):** For each `i`, `round_i.eval 0 + round_i.eval 1 = target_i`.
- `h_sat` at row `i` gives: `w[2i] + w[2i+1] + (other terms) = target_i`.
- By `hw`: `w[2i] = rounds i .prover_poly.eval 0` and `w[2i+1] = ... .eval 1`.
- The "other terms" for i > 0 are `-(1-r_{i-1}) * w[2(i-1)] - r_{i-1} * w[2(i-1)+1]`.
- By `hw` again and the degree-≤-1 property: `(1-r) * p.eval 0 + r * p.eval 1 = p.eval r` for deg-≤-1 poly. So the other terms = `-(rounds (i-1)).prover_poly.eval (challenges (i-1))`.
- Rearranging: `rounds_i.eval 0 + rounds_i.eval 1 = rounds_{i-1}.eval(r_{i-1})`. ✓

**Conjunct 2 (final eval):** `(rounds last).prover_poly.eval (challenges last) = p.eval challenges`.
- From `h_final`: `(1-r_{last}) * w[2*last] + r_{last} * w[2*last+1] = p.eval challenges`.
- By `hw` and degree-≤-1: LHS = `(rounds last).prover_poly.eval (challenges last)`. ✓

The key helper lemma needed:

```lean
/-- For a degree-≤-1 polynomial: p(r) = (1-r)·p(0) + r·p(1). -/
theorem eval_deg_le_one (p : F[X]) (hdeg : p.natDegree ≤ 1) (r : F) :
    p.eval r = (1 - r) * p.eval 0 + r * p.eval 1 := by
  sorry -- proved in Step 4
```

- [ ] **Step 4: Prove `eval_deg_le_one`**

Strategy: A polynomial with `natDegree ≤ 1` has the form `C a + C b * X` for some `a, b`.
- `p.eval 0 = a`
- `p.eval 1 = a + b`
- `p.eval r = a + b * r`
- `(1-r)*a + r*(a+b) = a - r*a + r*a + r*b = a + b*r` ✓

Use `Polynomial.eq_C_add_X_mul_C_of_natDegree_le_one` or manually decompose:
```lean
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_add_X_mul_of_natDegree_le_one hdeg
  simp [eval_add, eval_mul, eval_C, eval_X]
  ring
```

Note: the exact Mathlib lemma name may differ. Search for `natDegree_le_one` or `degree_le_one`. If no such decomposition exists, prove it by showing `p = C (p.eval 0) + C (p.eval 1 - p.eval 0) * X` using `Polynomial.ext` on coefficients.

- [ ] **Step 5: Prove `constraints_encode_sumcheck`**

Using `eval_deg_le_one` and the witness encoding, unfold the constraint satisfaction and show each conjunct of `verifierAccepts` holds.

If the full proof is too complex (lots of index arithmetic with `witnessSize`, `2*i`, etc.), use `sorry` for the hardest subgoals and report DONE_WITH_CONCERNS.

- [ ] **Step 6: Prove the reverse direction (correctness of constraint generation)**

```lean
/-- **Reverse bridge:** if verifierAccepts holds, then the encoded witness
    satisfies the generated constraints.
    This plus the forward direction gives: constraint satisfaction ↔ sumcheck acceptance. -/
theorem sumcheck_encodes_constraints {n : ℕ}
    (claimed_sum : F) (challenges : Fin n → F)
    (rounds : Fin n → SumcheckRound F)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_challenges : ∀ i, (rounds i).challenge = challenges i)
    (haccept : verifierAccepts p claimed_sum rounds) :
    satisfiesLinear (encodeWitness rounds) (generateConstraints claimed_sum challenges) := by
  sorry -- same structure as forward direction, reversed
```

- [ ] **Step 7: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 8: Commit**

```bash
git add LeanLongfellow/Ligero/Generate.lean
git commit -m "feat(Ligero): constraint generation from sumcheck, prove bridge theorem"
```

---

### Task 4: End-to-End Longfellow Soundness

**Files:**
- Create: `LeanLongfellow/Ligero/Longfellow.lean`

- [ ] **Step 1: Create `Longfellow.lean` with verifier and soundness theorems**

```lean
import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Generate
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F]

/-! # End-to-End Longfellow Soundness

If the abstract Ligero binding property holds, the Longfellow verifier
never accepts a wrong claim. The soundness error equals Ligero's
binding failure probability. -/

/-- The Longfellow verifier: checks Ligero proof against constraints
    generated from the sumcheck transcript.
    
    In the real protocol, the verifier does NOT run sumcheck separately —
    the sumcheck correctness is encoded in the linear constraints
    that Ligero checks. -/
def longfellowVerifierAccepts
    [L : LigeroScheme F (witnessSize n) m q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (ligeroCommit : L.Commitment)
    (lcs : LinearConstraints F m (witnessSize n))
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (ligeroProof : L.Proof) : Prop :=
  -- Constraints match the sumcheck transcript
  lcs = generateConstraints claimed_sum challenges ∧
  -- Ligero verifier accepts
  L.verify ligeroCommit lcs qcs ligeroProof

/-- **Deterministic Longfellow soundness:**
    If Ligero binding holds (axiom in LigeroScheme), the Longfellow verifier
    NEVER accepts a wrong claim.
    
    Proof: Ligero accept → binding → witness satisfies constraints
    → constraints encode sumcheck → claimed_sum is correct. -/
theorem longfellow_soundness_det
    [L : LigeroScheme F (witnessSize n) m q]
    (p : MultilinearPoly F n)
    (claimed_sum : F)
    (challenges : Fin n → F)
    (w : Fin (witnessSize n) → F)
    (rounds : Fin n → SumcheckRound F)
    -- Witness was encoded from the sumcheck transcript
    (hw : w = encodeWitness rounds)
    -- Degree bound on round polynomials
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    -- Challenges match
    (h_challenges : ∀ i, (rounds i).challenge = challenges i)
    -- Ligero proof and commitment
    (ligeroProof : L.Proof)
    (lcs : LinearConstraints F m (witnessSize n))
    (qcs : Fin q → QuadConstraint (witnessSize n))
    -- Longfellow verifier accepted
    (haccept : longfellowVerifierAccepts p claimed_sum challenges
      (L.commit w) lcs qcs ligeroProof)
    -- Final eval constraint also satisfied
    (h_final : satisfiesLinear w (generateFinalConstraint p challenges)) :
    claimed_sum = ∑ b : Fin n → Bool, p.table b := by
  sorry -- proved in Step 2

/-- **Corollary:** a wrong claim is never accepted. -/
theorem longfellow_no_false_accept
    [L : LigeroScheme F (witnessSize n) m q]
    (p : MultilinearPoly F n)
    (claimed_sum : F)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    -- ... (same hypotheses as above)
    (haccept : longfellowVerifierAccepts p claimed_sum challenges
      (L.commit w) lcs qcs ligeroProof)
    (h_final : satisfiesLinear w (generateFinalConstraint p challenges)) :
    False := by
  exact hclaim (longfellow_soundness_det p claimed_sum challenges w rounds
    hw hdeg h_challenges ligeroProof lcs qcs haccept h_final)
```

- [ ] **Step 2: Prove `longfellow_soundness_det`**

Strategy:
1. From `haccept`: extract `lcs = generateConstraints ...` and `L.verify (L.commit w) lcs qcs ligeroProof`
2. By `L.binding`: `satisfiesAll w lcs qcs`
3. Extract `satisfiesLinear w lcs` from `satisfiesAll`
4. By `constraints_encode_sumcheck` (with `hw`, `hdeg`, `h_challenges`, `h_sat`, `h_final`): `verifierAccepts p claimed_sum rounds`
5. By `sumcheck_completeness` logic or direct extraction: the claimed sum equals the table sum

Wait — step 5 is wrong. `verifierAccepts` doesn't directly give us `claimed_sum = ∑ table`. It says the verifier's checks pass. We need: if the verifier accepts AND the rounds are the honest prover's rounds, then the claim is correct. But the rounds here are the adversary's.

**Correction:** The bridge theorem `constraints_encode_sumcheck` says: constraint satisfaction → `verifierAccepts`. But we want the REVERSE: constraint satisfaction → claim is correct.

The correct chain is:
1. Ligero binding → `satisfiesLinear w (generateConstraints claimed_sum challenges)`
2. Unfolding `satisfiesLinear` at row 0: `w[0] + w[1] = claimed_sum`
3. By `hw`: `w[0] + w[1] = rounds_0.eval 0 + rounds_0.eval 1`
4. Unfolding through all constraints telescopically: the entire chain reduces to `claimed_sum = (some function of the witness that equals ∑ table when constraints are satisfied)`

Actually, the simplest path:
1. Binding → constraints satisfied → `verifierAccepts p claimed_sum rounds`
2. Combined with `h_final` (final eval check): the full `verifierAccepts` holds
3. `verifierAccepts` with the honest claim means... hmm, `verifierAccepts` holds for ANY accepted claim, not just the correct one.

**The real argument:** The constraints don't just encode `verifierAccepts`. They encode that the witness IS the honest transcript for `claimed_sum`. Combined with the final eval check, this pins `claimed_sum` to the correct value.

Let me simplify: prove `longfellow_soundness_det` directly from the constraint definitions without going through `verifierAccepts`:

1. `h_sat` at row 0: `w[0] + w[1] = claimed_sum` (sum check)
2. `h_sat` at row i > 0: `w[2i] + w[2i+1] = (1-r_{i-1})*w[2(i-1)] + r_{i-1}*w[2(i-1)+1]` (telescoping)
3. `h_final`: `(1-r_{last})*w[2*last] + r_{last}*w[2*last+1] = p.eval(challenges)` (final eval)
4. Iterating steps 1-2: `claimed_sum = (1-r_0)*w[0] + r_0*w[1]` at step 1... no, that's going the wrong direction.

**The correct direction:** The final constraint gives `p.eval(challenges)` in terms of the last witness entries. The telescoping goes backwards from the last to the first. At the first: `w[0] + w[1] = claimed_sum`. The telescoping and final constraint together force `claimed_sum` to equal the value derived from `p.eval(challenges)` through the sumcheck reduction.

This is exactly what `verifierAccepts` encodes! So the proof is:
1. Constraint satisfaction → `verifierAccepts` (by `constraints_encode_sumcheck`)
2. But `verifierAccepts` alone doesn't give correctness — a cheating prover can also make the verifier accept.

**Key insight I missed:** Ligero's binding guarantees the witness entries ARE the actual polynomial evaluations. Combined with degree ≤ 1, this means the round polynomials are fully determined. The constraints force them to be the HONEST polynomials, not just any polynomials passing the verifier.

Actually no — the witness just stores eval-at-0 and eval-at-1. Any degree-≤-1 polynomial is determined by these two values. So the witness fully determines the round polynomials. The constraints say: these polynomials telescope correctly AND the final eval matches `p.eval(challenges)`. This IS the sumcheck verifier check. And `sumcheck_completeness` says the honest prover passes. `sumcheck_soundness_det` says a wrong claim fails.

But we're going the other direction: we know constraints hold → we want claim correct. The missing link: constraints hold implies verifierAccepts. And then? `verifierAccepts` with wrong claim → root hit. But we need BOTH verifierAccepts AND "no root hit" to conclude the claim is correct.

**Simplest correct proof:** Don't go through `verifierAccepts` at all. Prove directly from the constraint telescoping:

By induction on the constraint chain:
- Row 0: `w[0] + w[1] = claimed_sum`
- Final: `(1-r_{n-1})*w[2(n-1)] + r_{n-1}*w[2(n-1)+1] = p.eval(challenges)`
- Telescoping rows: `w[2i] + w[2i+1] = (1-r_{i-1})*w[2(i-1)] + r_{i-1}*w[2(i-1)+1]`

Iterating: `claimed_sum = w[0] + w[1]`. And from the chain, `w[0] + w[1]` eventually equals something derived from `p.eval(challenges)`. But the chain doesn't directly give `claimed_sum = ∑ p.table` — it gives that the sumcheck VERIFIER would accept, which is necessary but not sufficient.

**The actual protocol handles this differently.** In real Longfellow, the claimed sum IS `0` (circuit outputs are zero). The verifier checks that constraint satisfaction implies the output is zero. The constraints encode this directly.

For our abstract version: the simplest correct formulation is that `longfellow_soundness_det` proves `verifierAccepts p claimed_sum rounds`, and then the user applies `sumcheck_soundness_det` if they want to show the claim is correct. The end-to-end statement becomes:

"If Ligero binding holds, the Longfellow verifier accepts only transcripts that would also pass the interactive sumcheck verifier."

This is the RIGHT theorem — it reduces Longfellow's soundness to the interactive sumcheck's soundness.

```lean
theorem longfellow_soundness_det ... :
    verifierAccepts p claimed_sum rounds
```

Then `sumcheck_soundness_det` handles the rest.

- [ ] **Step 3: Prove the combined corollary**

```lean
/-- Combined: Ligero binding + sumcheck soundness → wrong claim has root hit. -/
theorem longfellow_combined_soundness
    [L : LigeroScheme F (witnessSize n) m q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    -- ... witness, rounds, encoding, degree, challenges hypotheses ...
    (haccept : longfellowVerifierAccepts ...) :
    ∃ i, ∃ diff, diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (rounds i).challenge = 0 := by
  have hva := longfellow_soundness_det ...
  exact sumcheck_soundness_det p claimed_sum rounds hn hclaim hva hdeg
```

- [ ] **Step 4: Verify proofs compile**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`

- [ ] **Step 5: Commit**

```bash
git add LeanLongfellow/Ligero/Longfellow.lean
git commit -m "feat(Ligero): prove end-to-end Longfellow soundness"
```

---

### Task 5: Root Imports and Final Verification

**Files:**
- Modify: `LeanLongfellow.lean`

- [ ] **Step 1: Update root imports**

Add to `LeanLongfellow.lean`:

```lean
import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Generate
import LeanLongfellow.Ligero.Longfellow
```

- [ ] **Step 2: Full build and sorry check**

Run: `source ~/.elan/env && cd /data/Develop/lean-longfellow && lake build`
Run: `grep -rn "sorry" LeanLongfellow/Ligero/`

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow.lean
git commit -m "chore: add Ligero imports to root module"
```

---

## Spec Coverage Checklist

| Spec Item | Task |
|-----------|------|
| `LinearConstraints`, `QuadConstraint` | Task 1 |
| `satisfiesLinear`, `satisfiesQuad`, `satisfiesAll` | Task 1 |
| `LigeroScheme` typeclass | Task 2 |
| `binding` axiom | Task 2 |
| `encodeWitness` | Task 3 |
| `generateConstraints`, `generateFinalConstraint` | Task 3 |
| `constraints_encode_sumcheck` (bridge) | Task 3 |
| `eval_deg_le_one` (helper) | Task 3 |
| `longfellowVerifierAccepts` | Task 4 |
| `longfellow_soundness_det` | Task 4 |
| `longfellow_combined_soundness` | Task 4 |

## Dependency Graph

```
Task 1 (Constraints) → Task 2 (Interface) → Task 3 (Generate) → Task 4 (Longfellow) → Task 5 (Root)
```

Tasks 1 and 2 are small and mechanical. Task 3 is the hardest (witness encoding + bridge theorem). Task 4 composes everything.

## Expected Sorry's

- `constraints_encode_sumcheck` (Task 3) — the index arithmetic with `witnessSize`, `2*i`, `2*i+1` is tedious. May need sorry for the most mechanical parts.
- `eval_deg_le_one` (Task 3) — depends on Mathlib's API for decomposing degree-≤-1 polynomials. Should be provable but the exact lemma name may need hunting.
