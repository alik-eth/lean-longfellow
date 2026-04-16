# Track A: Close All Legitimate Gaps from Gemini Adversarial Review

**Date:** 2026-04-16
**Scope:** Four phases addressing review items #1/#4, #11, #5, #10
**Sequence:** Phase 1 → Phase 2 (parallel-safe) → Phase 3 (depends on 1+2) → Phase 4

---

## Context: What the Review Got Wrong

The Gemini review's headline claim ("the crown jewel is hollow") is **factually incorrect**.
The reviewer examined `Spec.lean:98-111` and found the `extraction` field, concluding it
was an unproved assumption. They missed two files:

- **`Composition.lean`** — builds `ecdsaCircuitSpec` (s=1, NL=1) with proved extraction
  via the coefficient-encoding trick: layer consistency + output=1 implies
  `ecdsaCoefficient ≠ 0` implies `ecdsaVerify`.
- **`GateComposition.lean`** — builds `ecdsaGateCircuitSpec` (s=5, NL=14n+7) with
  proved extraction for the full gate-level circuit (219 lines, no sorry).

The stale comment at `Spec.lean:16` ("building a concrete instance is future work") is
misleading and should be updated.

Similarly, the review's #2 (LigeroScheme binding is tautological) missed
`ProbabilisticBinding.lean` which proves `niLigero_binding_or_bad` from first principles
with error bound ≤ 2/|F|. The typeclass is an interface; the real proof bypasses it.

The review's #3 (hash injectivity vacuous) acknowledges the `_or_collision` variants but
dismisses them as "never actually asserting security" — this misunderstands
collision-extracting reductions, which are the standard non-vacuous formulation for
finite-field hash modeling.

---

## Phase 1: EllipticCurve Group Laws + P-256 E2E Integration

**Addresses:** Review items #1 (ECDSA extraction) and #4 (EllipticCurve unmoored)
**Goal:** Make `ecdsaVerify` meaningful by ensuring the `EllipticCurve` typeclass carries
group law axioms, and wire the concrete P-256 instance through to the end-to-end theorem.

### 1.1 Current State

- `EllipticCurve F` (Spec.lean:27-48) has abstract `scalarMul`, `pointAdd`, `xCoord`,
  `identity`, `fieldToNat` but **no axioms** connecting them.
- `CurveInstantiation.lean` defines P-256 params, proves discriminant ≠ 0, proves
  `p256_ecAdd_correct` (circuit add = Mathlib add when x1 ≠ x2).
- `P256CurveInstantiation.lean` has Pocklington primality for group order.
- **Gap:** No group laws in the typeclass. No `EllipticCurve` instance for P-256.
  No P-256-specific E2E theorem.

### 1.2 Design

**Step A: Extend `EllipticCurve` with group law axioms.**

Add to the typeclass (or create `EllipticCurveGroup extends EllipticCurve`):

```
-- Identity laws
pointAdd_identity_left : pointAdd identity P = P
pointAdd_identity_right : pointAdd P identity = P

-- Scalar multiplication laws
scalarMul_zero : scalarMul 0 P = identity
scalarMul_succ : scalarMul (n + 1) P = pointAdd P (scalarMul n P)

-- Commutativity (needed for ECDSA: u1·G + u2·Q = u2·Q + u1·G)
pointAdd_comm : pointAdd P Q = pointAdd Q P

-- fieldToNat round-trip (for ZMod p where p is prime)
fieldToNat_injective : Function.Injective fieldToNat
```

**Decision: extend `EllipticCurve` directly** rather than a subclass. The typeclass is only
used for ECDSA, and all meaningful instances will have group laws. Adding a subclass would
require updating every use site for no benefit.

Note: full associativity (`pointAdd_assoc`) is expensive to prove for Weierstrass curves.
We include only the axioms actually used by `ecdsaVerify` and its correctness chain.
Specifically, the ECDSA verification only needs: scalar mul unfolds correctly,
point addition is commutative (for R = u1·G + u2·Q), and fieldToNat is injective
(so field elements faithfully map to scalars).

**Step B: Build P-256 `EllipticCurve` instance.**

Bridge the existing `CurveInstantiation.lean` machinery to produce an `EllipticCurve`
instance:

- `Point := Mathlib WeierstrassCurve.Point p256WCurve` (or the existing `ECPoint` wrapper)
- `generator := p256Generator` (the NIST P-256 base point)
- `groupOrder := p256GroupOrder` (already proved prime via Pocklington)
- `scalarMul` and `pointAdd` delegate to Mathlib's group operations
- Group laws follow from Mathlib's `AddCommGroup` instance on `WeierstrassCurve.Point`
- `fieldToNat := ZMod.val` with injectivity from `ZMod.val_injective`

**Step C: P-256-specific E2E theorem.**

Add to `EndToEnd.lean` (or a new `P256EndToEnd.lean`):

```
theorem zkEidas_p256_soundness_or_collision
    [PoseidonHash F_p256 3] [PoseidonHash F_p256 1]
    [CRHash (EscrowFields F_p256) F_p256] ...
    (proof : ZkEidasFullProof F_p256 s NL) ... :
    (ecdsaVerify proof.z proof.Q proof.sig ∧ ...) ∨
    PoseidonCollision F_p256 3 ∨ ...
```

This eliminates the abstract `[EllipticCurve F]` parameter — the theorem speaks directly
about P-256.

**Step D: Fix stale comment.**

Update `Spec.lean:14-16` to reference the concrete instances in `Composition.lean` and
`GateComposition.lean`.

### 1.3 Files

| Action | File |
|--------|------|
| Modify | `Circuit/ECDSA/Spec.lean` — add group law axioms, fix comment |
| Modify | `Circuit/EC/CurveInstantiation.lean` — build `EllipticCurve` P-256 instance |
| Possibly modify | `Circuit/EC/P256CurveInstantiation.lean` — if group order lemmas needed |
| Create or modify | `P256EndToEnd.lean` or section in `EndToEnd.lean` |

### 1.4 Risk

The main risk is Mathlib API friction: `WeierstrassCurve.Point` may not directly expose
the group laws in the form we need. The bridge between `ECPoint` (circuit representation)
and Mathlib `Point` already exists (`ECPoint.toP256Point`), but going from Mathlib group
laws back to our `EllipticCurve` axioms requires care.

If `pointAdd_comm` or `scalarMul_succ` are hard to prove via Mathlib, we can:
- Use `native_decide` for specific values (not ideal)
- Weaken the axioms to only what `ecdsaVerify` needs
- Prove them as standalone lemmas rather than typeclass fields

---

## Phase 2: Wire HashDerived into End-to-End

**Addresses:** Review item #11 (Fiat-Shamir ROM gap)
**Goal:** Connect `FiatShamir/HashDerived.lean` to the E2E composition so the main
theorem explicitly covers hash-derived challenges.

### 2.1 Current State

`HashDerived.lean` (300 lines) is complete and proves:
- `fiatShamir_hash_soundness`: same `n·d·|F|^(n-1)` bound for hash-derived challenges
- `rom_reduces_adaptive`: any `CommitBeforeChallenge` adversary gets the same bound
- `oracleRestriction_surjective`: every challenge vector arises from some oracle

`EndToEnd.lean` Section 8 re-exports `fiatShamir_soundness` directly but doesn't
reference `HashDerived.lean`.

### 2.2 Design

Add a new section (Section 8b) to `EndToEnd.lean`:

```
import LeanLongfellow.FiatShamir.HashDerived

-- Section 8b: Hash-derived Fiat-Shamir bound (ROM)
theorem zkEidas_fiatShamir_hash_bound [Fintype F] {n d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b, p.table b)
    (adv : NonAdaptiveAdversary F n)
    (hdeg : ∀ i, (adv.proof.round_polys i).natDegree ≤ d) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum adv.proof cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  fiatShamir_hash_soundness p claimed_sum hn hd hclaim adv hdeg

-- ROM reduction for commit-before-challenge adversaries
theorem zkEidas_rom_soundness [Fintype F] {n d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n) (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_cbc : CommitBeforeChallenge adversary) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) :=
  rom_reduces_adaptive p claimed_sum hn hd hclaim adversary hdeg h_cbc
```

This is a thin re-export but it closes the narrative gap: the E2E file explicitly
documents that hash-derived challenges are covered.

### 2.3 Files

| Action | File |
|--------|------|
| Modify | `EndToEnd.lean` — add import + Section 8b |

### 2.4 Risk

Minimal. This is a re-export of existing proved theorems.

---

## Phase 3: Concrete ε Bound

**Addresses:** Review item #5 (no single end-to-end probability bound)
**Goal:** Instantiate `longfellow_total_error` with concrete P-256 + gate-level ECDSA
parameters to produce a single numeric bound.

### 3.1 Current State

`ProbabilisticE2E.lean` proves `longfellow_total_error` with abstract parameters
`E_sc, E_lin, E_quad, E_ldt`. The per-component bounds exist:
- `gkr_layer_error_bound`: per-layer ≤ `(2s) · (2 · |F|^(2s-1))`
- `ligero_linear_error_bound`: ≤ `|F|^(m-1)`
- `ligero_quad_error_bound`: ≤ `|F|^(q-1)`
- `column_ldt_detection_probability` (in ReedSolomon/)

But nobody has plugged in concrete values.

### 3.2 Design

Create a new file `LeanLongfellow/ConcreteP256Bound.lean`:

**Step A: Define concrete parameters.**

```
-- From ecdsaGateCircuitSpec with n=256 (P-256 scalar bits):
def p256_NL : ℕ := ecdsaGateNL 256  -- = 14 * 256 + 7 = 3591
def p256_s : ℕ := 5                  -- gate circuit width

-- Ligero parameters (need to read from existing instantiation):
-- m = number of linear constraints
-- q = number of quadratic constraints
-- These come from the Ligero encoding of the circuit
```

**Step B: Compute the concrete total error.**

```
def p256ErrorParams : LongfellowErrorParams where
  num_layers := p256_NL
  sumcheck_error_per_layer := (2 * p256_s) * (2 * Fintype.card F_p256 ^ (2 * p256_s - 1))
  ligero_linear_error := Fintype.card F_p256 ^ (m - 1)
  ligero_quad_error := Fintype.card F_p256 ^ (q - 1)
  ligero_ldt_error := ldt_error_concrete

theorem p256_total_error :
    p256ErrorParams.total = <concrete number> := by native_decide  -- or norm_num
```

**Step C: Express as probability ratio.**

```
-- The total challenge space is |F|^n for some n
-- Probability ≤ total_error / |F|^n
-- For the sumcheck component with d=2, s=5:
--   per-layer error = 10 * 2 * |F|^9 = 20|F|^9
--   NL layers: 3591 * 20|F|^9 = 71820|F|^9
-- Ligero: 2/|F| (from niLigero_combined_error)
-- Total ε ≤ 71820/|F| + 2/|F| = 71822/|F|
-- For |F| ≈ 2^256: ε ≈ 71822 / 2^256 ≈ 2^{-239}

theorem p256_soundness_probability :
    p256ErrorParams.total ≤
      p256_NL * ((2 * p256_s) * (2 * Fintype.card F_p256 ^ (2 * p256_s - 1))) +
      Fintype.card F_p256 ^ (m - 1) +
      Fintype.card F_p256 ^ (q - 1) +
      ldt_error := by ring_nf
```

**Step D: Narrative theorem with simplified bound.**

```
-- Simplified upper bound: (4 * NL * s + 2) / |F|
-- This overapproximates the union bound for readability
theorem p256_simplified_bound :
    p256ErrorParams.total * 1 ≤ (4 * p256_NL * p256_s + 2) * Fintype.card F_p256 ^ (challenge_dim - 1) := by
  ...
```

### 3.3 Open Question: Ligero Parameters

The concrete Ligero parameters (m, q, LDT block size) depend on how the ECDSA circuit
is encoded as a Ligero tableau. This encoding may not be fully formalized. If not,
we can:

- **Option A:** Parameterize the bound by m, q and prove the simplified bound
  `ε ≤ (4·NL·s + 2)/|F|` which absorbs the Ligero terms.
- **Option B:** Fix m, q from the circuit structure and compute exactly.

Option A is recommended: it gives a clean single-ε theorem without requiring the
full Ligero encoding to be formalized.

### 3.4 Files

| Action | File |
|--------|------|
| Create | `LeanLongfellow/ConcreteP256Bound.lean` |
| Modify | `LeanLongfellow.lean` (root import file) — add import |

### 3.5 Depends On

- Phase 1 (for concrete NL, s values from ecdsaGateCircuitSpec)
- Phase 2 (for hash-derived error bound to reference in the narrative)

---

## Phase 4: Knowledge Soundness

**Addresses:** Review item #10 (no proof of knowledge / extractability)
**Goal:** Prove that a valid Longfellow proof implies the prover "knows" a witness.

### 4.1 Current State

No extractor, no PoK definition exists anywhere in the codebase.

### 4.2 Background

For Longfellow (GKR + Ligero), knowledge extraction works differently from
succinct proof systems:

1. The prover commits a **tableau** (matrix of field elements) via Merkle tree
2. The Ligero verifier opens specific columns and checks:
   - **LDT:** each row is close to a Reed-Solomon codeword
   - **Linear test:** random linear combination of columns satisfies constraints
   - **Quadratic test:** random quadratic combination satisfies constraints
3. If all tests pass, the committed values are (with high probability) a valid witness

The extractor's job: given a tableau that passes all three tests, decode the RS
codewords to recover the witness, and prove the recovered witness satisfies all
constraints.

### 4.3 Design

**Step A: Define the knowledge extractor.**

New file: `LeanLongfellow/Ligero/Extraction.lean`

```
/-- A knowledge extractor for Ligero: given a tableau that passes the
    three verification tests, recover the witness. -/
noncomputable def ligeroExtract
    (domain : Fin BLOCK → F)
    (T : Fin ROWS → Fin BLOCK → F)
    (h_wf : tableauWellFormed domain T) : Fin n → F :=
  -- Decode each row as an RS codeword to get coefficients
  -- Extract the witness from the first n coefficient positions
  fun i => rsDecodeCoefficient domain (T (rowOf i)) (colOf i)
```

The RS decoding machinery partially exists in `ReedSolomon/Decode.lean`.

**Step B: Prove extraction correctness.**

```
/-- If the tableau is well-formed (passes LDT), and the linear and quadratic
    tests accept, then the extracted witness satisfies all constraints. -/
theorem ligero_extraction_sound
    (domain : Fin BLOCK → F)
    (T : Fin ROWS → Fin BLOCK → F)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_wf : tableauWellFormed domain T)
    (h_lin : satisfiesLinear w lcs)
    (h_quad : ∀ i, satisfiesQuad w (qcs i))
    (h_commit : w = ligeroExtract domain T h_wf) :
    satisfiesAll w lcs qcs :=
  ⟨h_lin, h_quad⟩
```

Actually, the more interesting direction is the **probabilistic** version:

```
/-- Probabilistic knowledge extraction: if the verifier accepts with
    non-negligible probability over the challenges, then the extractor
    recovers a valid witness with overwhelming probability.

    More precisely: if the three tests pass for the committed tableau,
    then either the extracted witness satisfies all constraints, or
    the challenges landed in a bad set of measure ≤ 2/|F|. -/
theorem ligero_knowledge_extraction
    (domain : Fin BLOCK → F)
    (T : Fin ROWS → Fin BLOCK → F)
    (h_wf : tableauWellFormed domain T)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (challenges : ...) -- linear + quadratic challenges
    (h_accept : niLigeroVerify ...) :
    satisfiesAll (ligeroExtract domain T h_wf) lcs qcs ∨
    challenges ∈ badSet  -- with |badSet| ≤ 2 * |F|^(dim-1)
```

**Step C: Compose with GKR for full knowledge soundness.**

```
/-- Full Longfellow knowledge soundness: if the verifier accepts and
    challenges avoid the bad set, the prover knows a witness. -/
theorem longfellow_knowledge_soundness
    -- ... circuit params, Ligero params, challenges ...
    (h_accept : longfellowVerifierAccepts ...) :
    ∃ w, satisfiesAll w lcs qcs ∨ challenges ∈ badSet
```

**Step D: Connect to ECDSA E2E.**

```
/-- Knowledge-sound ECDSA: if the proof is accepted, the prover knows
    wire values that make the ECDSA circuit consistent. -/
theorem ecdsa_knowledge_soundness
    (spec : ECDSACircuitSpec F s NL z Q sig)
    (h_accept : ...) :
    ∃ values, (∀ k g, layerConsistent (spec.layers k) ...) ∧
    ecdsaVerify z Q sig
```

### 4.4 Approach: Straight-Line vs Rewinding

For Longfellow, we use **straight-line extraction** (no rewinding):

1. The Ligero commitment is opened at specific columns during verification
2. The extractor reads the full tableau (it's committed, not hidden)
3. RS decoding recovers the witness from the tableau

This is simpler than rewinding-based extraction because Ligero is a transparent
commitment scheme — the extractor can read the committed data directly.

The key insight: `niLigero_binding_or_bad` already proves that if the tests pass
and challenges are good, the committed witness satisfies the constraints. This IS
the extraction theorem — we just need to repackage it.

### 4.5 RS Decoding Requirements

The extractor needs RS decoding: given evaluations of a polynomial at BLOCK points,
recover the coefficients. This requires:

- `ReedSolomon/Decode.lean` (exists, need to check completeness)
- Unique decoding when the number of evaluation points exceeds 2·degree
- The decoding function + proof that decode ∘ encode = id

### 4.6 Files

| Action | File |
|--------|------|
| Create | `LeanLongfellow/Ligero/Extraction.lean` |
| Possibly modify | `LeanLongfellow/Ligero/ReedSolomon/Decode.lean` |
| Modify | `EndToEnd.lean` — add knowledge-sound E2E theorem |
| Modify | `LeanLongfellow.lean` — add import |

### 4.7 Depends On

- Existing RS decode machinery (need to audit)
- Phase 1 is NOT a dependency: knowledge extraction is about Ligero/RS, not EC group laws.
  However, the E2E knowledge-soundness theorem (Step D) references the ECDSA circuit,
  so the final integration step benefits from Phase 1 being done.

### 4.8 Risk

**Medium-high.** The RS decoding proof is the critical path. If `Decode.lean` is
incomplete, we may need significant new Mathlib lemmas about polynomial interpolation
and unique decoding. The straight-line extraction approach avoids rewinding complexity
but still requires the algebraic machinery.

If RS decoding proves too difficult, a fallback is to prove knowledge soundness
in the "oracle model" where the extractor has direct access to the committed
polynomial coefficients (bypassing the encoding step). This is weaker but still
meaningful.

---

## Dependency Graph

```
Phase 1 (EC group laws + P-256) ──→ Phase 3 (concrete ε) ←── Phase 2 (HashDerived wiring)

Phase 4 (knowledge soundness) — independent of 1/2, only needs RS decode audit
         └──→ E2E integration step benefits from Phase 1
```

Phase 1 and Phase 2 can run in parallel.
Phase 3 requires both 1 and 2.
Phase 4 core (Ligero extraction) is independent; its E2E integration benefits from Phase 1.

---

## Success Criteria

After all four phases, these theorems exist (sorry-free, axiom-free):

1. `EllipticCurve` typeclass has group law axioms; P-256 instance proves them via Mathlib.
2. `EndToEnd.lean` imports and re-exports `fiatShamir_hash_soundness` and
   `rom_reduces_adaptive`.
3. A concrete theorem: `Pr[Longfellow accepts false statement for P-256] ≤ ε` with
   `ε` a computable ratio involving `p256Prime`.
4. A knowledge-soundness theorem: if verifier accepts (challenges not in bad set),
   an extractor recovers a valid witness.

The Gemini review's scorecard entries change:
- "ECDSA circuit correctness: Missing" → **Proved** (was already proved, now with group laws)
- "Ligero binding (deterministic): Missing" → **Proved** (was already proved via probabilistic path)
- "End-to-end probability bound: Missing" → **Proved** (concrete ε)
- "Knowledge soundness: Missing" → **Proved** (straight-line extraction)
- "Fiat-Shamir ROM gap" → **Closed** (HashDerived wired in)
