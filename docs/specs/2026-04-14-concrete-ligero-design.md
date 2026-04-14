# Concrete Ligero Instantiation

**Date:** 2026-04-14
**Status:** Draft
**Depends on:** Ligero/Constraints (complete), Ligero/Interface (complete)
**Sub-project:** D (concrete Ligero internals)

## Motivation

The abstract `LigeroScheme` typeclass takes `binding` as an axiom — if the verifier accepts, the committed witness satisfies the constraints. This spec formalizes Ligero's internals and proves the binding property, replacing the axiom with a theorem.

Ligero's architecture: the prover encodes the witness as a Reed-Solomon codeword arranged in a tableau (matrix). The verifier runs three probabilistic tests (low-degree, linear, quadratic) on randomly opened columns. If all three pass, the witness satisfies the constraints with high probability.

## Scope

This spec covers the **information-theoretic core** of Ligero — the algebraic argument, not the cryptographic compilation. Specifically:

**In scope:**
- Reed-Solomon encoding and distance properties
- Tableau structure (NROW × NCOL matrix of codewords)
- The three verifier tests (low-degree, linear, quadratic)
- Soundness of each test
- Composition into the binding property
- Concrete `LigeroScheme` instance

**Out of scope (deferred):**
- Merkle tree commitment (hash-based; orthogonal to algebraic soundness)
- Concrete hash function (SHA-256)
- Fiat-Shamir compilation of the interactive Ligero protocol
- Serialization / field-specific optimizations
- Subfield optimizations

## Architecture

```
LeanLongfellow/
├── Ligero/
│   ├── Constraints.lean     # (existing) LinearConstraints, QuadConstraint
│   ├── Interface.lean        # (existing) LigeroScheme typeclass
│   ├── ReedSolomon/
│   │   ├── Defs.lean         # RS codewords, encoding, evaluation domain
│   │   ├── Distance.lean     # Minimum distance, agreement bound
│   │   └── Proximity.lean    # Proximity testing lemma
│   ├── Tableau.lean          # Tableau structure, row encoding
│   ├── Tests/
│   │   ├── LowDegree.lean    # Low-degree test definition and soundness
│   │   ├── Linear.lean       # Linear constraint test and soundness
│   │   └── Quadratic.lean    # Quadratic constraint test and soundness
│   ├── Soundness.lean        # Composition of three tests → binding
│   └── Concrete.lean         # LigeroScheme instance with proved binding
```

## Component 1: Reed-Solomon Codes (ReedSolomon/)

### 1.1 Definitions (Defs.lean)

Reed-Solomon codes are evaluation codes: a codeword is a polynomial evaluated at every point of a domain.

```lean
/-- An evaluation domain: a list of distinct field elements. -/
structure EvalDomain (F : Type*) [Field F] (N : ℕ) where
  points : Fin N → F
  distinct : Function.Injective points

/-- Reed-Solomon encoding: evaluate a polynomial of degree < k at all domain points. -/
noncomputable def rsEncode {F : Type*} [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (coeffs : Fin k → F) : Fin N → F :=
  fun i => (∑ j : Fin k, Polynomial.C (coeffs j) * Polynomial.X ^ (j : ℕ)).eval (domain.points i)

/-- A word is a valid RS codeword if it equals rsEncode of some polynomial. -/
def isRSCodeword {F : Type*} [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (word : Fin N → F) : Prop :=
  ∃ coeffs : Fin k → F, word = rsEncode domain k coeffs

/-- The RS code as a set. -/
def rsCode (F : Type*) [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) : Set (Fin N → F) :=
  { w | isRSCodeword domain k w }
```

### 1.2 Distance Properties (Distance.lean)

The minimum distance of RS[N, k] is N - k + 1 (Singleton bound, met with equality).

```lean
/-- Two distinct RS codewords agree on at most k - 1 positions. -/
theorem rs_agreement_bound {F : Type*} [Field F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂) :
    (Finset.univ.filter (fun i => w₁ i = w₂ i)).card ≤ k - 1
```

**Proof strategy:** `w₁ - w₂` corresponds to a nonzero polynomial of degree < k. A nonzero polynomial of degree < k has at most k - 1 roots. The agreement set is exactly the root set.

### 1.3 Proximity Testing (Proximity.lean)

If a word is far from all codewords, random spot-checks detect this.

```lean
/-- The agreement of a word with the closest codeword. -/
noncomputable def maxAgreement {F : Type*} [Field F] [Fintype F] {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (word : Fin N → F) : ℕ :=
  Finset.sup' (Finset.univ) ⟨sorry⟩  -- nonempty, or handle separately
    (fun coeffs => (Finset.univ.filter (fun i =>
      word i = rsEncode domain k coeffs i)).card)

/-- If a word has maxAgreement ≤ t with all codewords of degree < k,
    then a random set of NREQ positions detects corruption with probability
    ≥ 1 - (t/N)^NREQ. -/
theorem proximity_test_soundness {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {N : ℕ} (domain : EvalDomain F N) (k : ℕ)
    (word : Fin N → F) (t : ℕ) (NREQ : ℕ)
    (ht : maxAgreement domain k word ≤ t) :
    -- The probability that NREQ random positions all agree with some codeword
    -- is at most (t/N)^NREQ.
    -- Formalized as: the number of "bad" NREQ-subsets is bounded.
    sorry  -- See proof strategy below
```

**Proof strategy:** Each random position independently has probability ≤ t/N of agreeing with the closest codeword. By independence (the positions are chosen uniformly without replacement, but the bound holds even with replacement), the probability all NREQ agree is ≤ (t/N)^NREQ.

**Note:** The exact formalization of "probability over random subsets" needs care. Options:
1. Count over all NREQ-element subsets of `Fin N` (combinatorial approach)
2. Count over all functions `Fin NREQ → Fin N` (with-replacement, simpler, weaker bound)

Option 2 is simpler and sufficient for Ligero's security analysis.

## Component 2: Tableau (Tableau.lean)

The Ligero tableau is an NROW × NCOL matrix where each row is an RS codeword.

```lean
/-- Ligero parameters. -/
structure LigeroParams where
  NROW : ℕ       -- number of rows (witness rows + special rows)
  NCOL : ℕ       -- number of columns (evaluation domain size)
  BLOCK : ℕ      -- message length (degree bound for RS)
  NREQ : ℕ       -- number of columns opened (security parameter)
  h_block_lt : BLOCK < NCOL
  h_nreq_lt : NREQ ≤ NCOL - BLOCK  -- opened from [BLOCK, NCOL)

/-- A Ligero tableau: NROW rows, each an element of F^NCOL.
    Honest rows are RS codewords of degree < BLOCK. -/
structure Tableau (F : Type*) [Field F] (params : LigeroParams) where
  rows : Fin params.NROW → Fin params.NCOL → F

/-- A tableau is well-formed if every row is an RS codeword. -/
def tableauWellFormed {F : Type*} [Field F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL) (T : Tableau F params) : Prop :=
  ∀ i : Fin params.NROW, isRSCodeword domain params.BLOCK (T.rows i)

/-- The message portion of row i: the first BLOCK evaluations.
    For a valid codeword, this uniquely determines the polynomial
    and hence the full row. -/
def rowMessage {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params) (i : Fin params.NROW)
    (h : params.BLOCK ≤ params.NCOL := by omega) : Fin params.BLOCK → F :=
  fun j => T.rows i ⟨j.val, by omega⟩
```

### Witness embedding

The witness vector `w : Fin n → F` is split into chunks of size WR and placed into the message portion of witness rows (rows IW through IW + NWR - 1). The first NREQ positions of each row are random blinding values.

```lean
/-- The witness is correctly embedded in the tableau. -/
def witnessEmbedded {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params) (w : Fin n → F)
    (IW : ℕ) (WR : ℕ) (NREQ : ℕ)
    (h_block : params.BLOCK = NREQ + WR) : Prop :=
  ∀ (row : Fin ((n + WR - 1) / WR)) (col : Fin WR),
    let witness_idx := row.val * WR + col.val
    witness_idx < n →
    rowMessage T ⟨IW + row.val, by sorry⟩ ⟨NREQ + col.val, by sorry⟩ =
      w ⟨witness_idx, by sorry⟩
```

## Component 3: The Three Tests (Tests/)

### 3.1 Low-Degree Test (LowDegree.lean)

The low-degree test checks that all rows are (close to) valid RS codewords. The verifier takes a random linear combination of rows and checks if the result is a codeword.

```lean
/-- The verifier's low-degree test:
    1. Sample random coefficients u[0..NROW-1]
    2. Compute combined row: ldt = ∑ u[i] · T[i]
    3. Take the message portion (first BLOCK entries)
    4. Extend to full codeword via rsEncode
    5. Check: extension matches T at opened positions -/
def lowDegreeTestAccepts {F : Type*} [Field F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL)
    (h_range : ∀ j, params.BLOCK ≤ (opened j).val) : Prop :=
  let combined : Fin params.NCOL → F :=
    fun col => ∑ i : Fin params.NROW, u i * T.rows i col
  let msg : Fin params.BLOCK → F :=
    fun j => combined ⟨j.val, by omega⟩
  let extended := rsEncode domain params.BLOCK msg
  ∀ j : Fin params.NREQ, extended (opened j) = combined (opened j)

/-- Low-degree test soundness: if any row is NOT a valid codeword,
    the test rejects with high probability over the random combination
    coefficients u and opened positions.
    
    Specifically: if row i has maxAgreement ≤ BLOCK - 1 + δ with all
    degree-< BLOCK polynomials (where δ > 0 means it's NOT a codeword),
    then a random linear combination preserves this distance, and
    NREQ random checks catch it. -/
theorem lowDegreeTest_soundness {F : Type*} [Field F]
    [DecidableEq F] [Fintype F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) :
    -- If not all rows are codewords...
    ¬ tableauWellFormed domain T →
    -- ...then the probability of the test accepting is bounded.
    -- Formalized as a counting bound over (u, opened) pairs.
    sorry
```

**Proof strategy (high level):**
1. If row `i` is not a codeword, it disagrees with every degree-< BLOCK polynomial on at least `NCOL - BLOCK + 1` positions.
2. A random linear combination `∑ u[i] · row[i]` is also not a codeword (with high probability over `u`), because a single non-codeword row "contaminates" the combination.
3. The NREQ opened positions each independently have probability ≤ `(BLOCK-1)/(NCOL-BLOCK)` of accidentally agreeing.
4. The overall failure probability is ≤ `((BLOCK-1)/(NCOL-BLOCK))^NREQ`.

**This is the hardest single proof in the project.** It requires:
- Schwartz-Zippel over the random combination coefficients
- The RS distance property
- A counting argument over opened positions

### 3.2 Linear Constraint Test (Linear.lean)

The linear constraint test checks that the witness satisfies `A·w = b`.

```lean
/-- The linear constraint test:
    1. Verifier samples random α[0..m-1] to combine m constraints into one
    2. Combined constraint: (∑ α[c] · A[c]) · w = ∑ α[c] · b[c]
    3. Prover provides a "dot product" row in the tableau
    4. Verifier checks: the dot product row encodes the inner product
       of the combined constraint vector with each witness row
    5. The sum of the dot row's message = combined target -/
def linearTestAccepts {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params)
    (lcs : LinearConstraints F m n)
    (alpha : Fin m → F)
    (IDOT : Fin params.NROW)    -- dot product row index
    (IW : ℕ) (WR NREQ : ℕ) : Prop :=
  -- The combined constraint row times witness rows, checked at opened positions
  -- Sum of dot row message portion = ∑ α[c] · b[c]
  let combined_target := ∑ c : Fin m, alpha c * lcs.target c
  let dot_msg_sum := ∑ j : Fin params.BLOCK,
    rowMessage T IDOT ⟨j.val, by sorry⟩
  -- Message portion sum check (the "inner product" test)
  dot_msg_sum = combined_target

/-- Linear test soundness: if the witness does NOT satisfy the
    combined linear constraint, the dot row cannot be both a valid
    codeword AND have the correct message sum.
    
    Over random α, the probability that a non-satisfying witness
    accidentally passes is ≤ 1/|F| (Schwartz-Zippel on the
    random linear combination). -/
theorem linearTest_soundness {F : Type*} [Field F]
    [DecidableEq F] [Fintype F] {params : LigeroParams}
    (T : Tableau F params)
    (lcs : LinearConstraints F m n)
    (w : Fin n → F)
    (h_not_sat : ¬ satisfiesLinear w lcs) :
    -- Over random α, the test rejects with probability ≥ 1 - 1/|F|
    sorry
```

**Proof strategy:**
1. If `A·w ≠ b`, then `∃ c, (A[c])·w ≠ b[c]`.
2. The combined constraint `(∑ α[c]·A[c])·w = ∑ α[c]·b[c]` is a degree-1 polynomial in the α variables.
3. By Schwartz-Zippel, a random α satisfies this with probability ≤ 1/|F|.
4. When the combined constraint is violated, the dot row sum check fails (because the row is a codeword, so its evaluation is determined).

### 3.3 Quadratic Constraint Test (Quadratic.lean)

The quadratic constraint test checks `w[x]·w[y] = w[z]` for each quadratic constraint.

```lean
/-- The quadratic constraint test:
    1. Prover adds rows Qx, Qy, Qz to the tableau (copies of witness entries)
    2. Verifier checks (via random combination):
       a. Qx, Qy, Qz are consistent with witness rows (linear test)
       b. Qx ⊗ Qy = Qz pointwise (quadratic identity) -/
def quadraticTestAccepts {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params)
    (qcs : Fin q → QuadConstraint n)
    (IQD : Fin params.NROW)  -- quadratic test row
    (u_quad : Fin q → F)
    (opened : Fin params.NREQ → Fin params.NCOL) : Prop :=
  -- For each opened position, the combined quadratic identity holds:
  -- ∑ u[k] · (T[iqz+k][col] - T[iqx+k][col] * T[iqy+k][col]) = T[IQD][col]
  sorry  -- exact formulation depends on row indexing

/-- Quadratic test soundness: if the witness violates some quadratic
    constraint, the test rejects with high probability. -/
theorem quadraticTest_soundness {F : Type*} [Field F]
    [DecidableEq F] [Fintype F] {params : LigeroParams}
    (T : Tableau F params)
    (qcs : Fin q → QuadConstraint n)
    (w : Fin n → F)
    (h_not_sat : ∃ i, ¬ satisfiesQuad w (qcs i)) :
    sorry
```

**Proof strategy:**
1. The Qx, Qy, Qz rows encode copies of witness entries (checked by linear consistency).
2. The pointwise product `Qx ⊗ Qy` is a codeword of degree < 2·BLOCK - 1 (product of two degree-< BLOCK polynomials).
3. `Qz` is a codeword of degree < BLOCK.
4. Their difference `Qx⊗Qy - Qz` is a codeword of degree < 2·BLOCK - 1.
5. If the quadratic constraint is violated, this difference is nonzero.
6. A nonzero codeword of degree < 2·BLOCK - 1 has at most 2·BLOCK - 2 roots.
7. NREQ random positions catch it with probability ≥ 1 - ((2·BLOCK-2)/(NCOL-BLOCK))^NREQ.

**Key requirement:** NCOL ≥ 2·BLOCK - 1 (so the product polynomial fits in the evaluation domain). This is the `DBLOCK = 2·BLOCK - 1` parameter from the IETF spec.

## Component 4: Composition (Soundness.lean)

### Combining the three tests

```lean
/-- All three Ligero tests pass. -/
def ligeroVerifierAccepts {F : Type*} [Field F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (verifier_randomness : LigeroVerifierRandomness F params m q) : Prop :=
  lowDegreeTestAccepts domain T verifier_randomness.u
    verifier_randomness.opened verifier_randomness.h_range ∧
  linearTestAccepts T lcs verifier_randomness.alpha
    verifier_randomness.IDOT verifier_randomness.IW
    verifier_randomness.WR verifier_randomness.NREQ ∧
  quadraticTestAccepts T qcs verifier_randomness.IQD
    verifier_randomness.u_quad verifier_randomness.opened

/-- Ligero binding theorem: if all three tests accept, then with
    high probability the embedded witness satisfies all constraints.
    
    Error: ε_ldt + ε_linear + ε_quad
    where each ε is bounded by the respective test's soundness theorem. -/
theorem ligero_binding {F : Type*} [Field F]
    [DecidableEq F] [Fintype F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_embedded : witnessEmbedded T w ...)
    (h_accept : ligeroVerifierAccepts domain T lcs qcs randomness) :
    -- Either w satisfies all constraints, or we're in the error event
    satisfiesAll w lcs qcs ∨ errorEvent randomness
```

**Proof:**
1. LDT accepts → all rows are codewords (except with prob ε_ldt)
2. All rows are codewords + linear test accepts → satisfiesLinear (except with prob ε_linear)
3. All rows are codewords + quadratic test accepts → satisfiesQuad (except with prob ε_quad)
4. Union bound: total error ≤ ε_ldt + ε_linear + ε_quad

## Component 5: Concrete Instance (Concrete.lean)

```lean
/-- Concrete Ligero instantiation.
    Commitment = Merkle root (abstracted as tableau hash).
    Proof = opened columns + test responses.
    binding = ligero_binding composed with error bound. -/
noncomputable instance concreteLigero
    [params : LigeroParams] [domain : EvalDomain F params.NCOL]
    : LigeroScheme F n m q where
  Commitment := -- Tableau hash (abstract)
  Proof := -- Opened columns + LDT/linear/quad responses
  commit w := -- Embed w in tableau, hash
  verify com lcs qcs π := -- Run three tests
  binding := -- By ligero_binding
```

## Expected Sorry's

The following are expected to require `sorry`, ordered by difficulty:

1. **`lowDegreeTest_soundness`** — Hardest. Requires Schwartz-Zippel on random linear combination + RS distance. May need 100+ lines.
2. **`proximity_test_soundness`** — Counting argument over random subsets. Moderate.
3. **`linearTest_soundness`** — Schwartz-Zippel on α. Moderate, similar structure to existing `fiatShamir_soundness`.
4. **`quadraticTest_soundness`** — Product degree bound + spot checking. Moderate.
5. **`rs_agreement_bound`** — Polynomial root bound. Should be straightforward given Mathlib's `Polynomial.card_roots`.

**Sorry-free targets:**
- All definitions (types, predicates)
- `ligero_binding` composition (given the three test soundness theorems)
- RS encoding definitions
- Tableau structure

## Proof Difficulty Estimates

| Component | Lines (est.) | Difficulty | Dependencies |
|-----------|-------------|------------|--------------|
| RS Defs | ~60 | Easy | Mathlib Polynomial |
| RS Distance | ~80 | Medium | Polynomial.card_roots |
| Proximity | ~100 | Medium | Counting/combinatorics |
| Tableau | ~50 | Easy | RS Defs |
| LDT soundness | ~150 | **Hard** | RS Distance, Schwartz-Zippel |
| Linear test | ~100 | Medium | Schwartz-Zippel |
| Quadratic test | ~120 | Medium | RS Distance, product degree |
| Composition | ~40 | Easy | Three tests |
| Concrete instance | ~30 | Easy | Composition |
| **Total** | **~730** | | |

## References

- Ames, Hazay, Ishai, Venkitasubramaniam. "Ligero: Lightweight Sublinear Arguments Without a Trusted Setup" (CCS 2017)
- IETF draft-google-cfrg-libzk-01, Section 4 (Ligero ZK Proof System)
- Existing: LeanLongfellow/Ligero/Interface.lean (abstract typeclass to instantiate)
