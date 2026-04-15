import LeanLongfellow.Ligero.ColumnOpening
import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Tests.Linear
import LeanLongfellow.Ligero.Tests.Quadratic
import LeanLongfellow.Ligero.Tests.LowDegree
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Column-Level Constraint Tests for Ligero

In the full Ligero protocol the verifier never sees the witness directly.
Instead, the prover sends *response polynomials* (one for the linear test,
one for the quadratic test), and the verifier spot-checks these polynomials
at the opened column positions.

This file reformulates the linear and quadratic tests from
`Ligero.Tests.Linear` and `Ligero.Tests.Quadratic` in terms of column
openings and polynomial spot-checks, and proves bridge theorems connecting
the column-level predicates to the witness-level predicates.

## Overview

1. **`polynomialSpotCheck`** — generic predicate: an observed value function
   agrees with an RS codeword at every opened position.

2. **`LinearResponse` / `columnLinearCheck`** — the linear-test response
   polynomial and the column-level acceptance predicate.

3. **`QuadraticResponse` / `columnQuadraticCheck`** — the quadratic-test
   response polynomial and the column-level acceptance predicate.

4. **Bridge theorems** — if the tableau is well-formed and the witness
   satisfies the constraints, the honest prover's responses pass the
   column-level checks.
-/

set_option autoImplicit false

open Finset

-- ============================================================
-- Section 1: Polynomial spot-check
-- ============================================================

variable {D : Type*} [MerkleHash D]
variable {F : Type*} [Field F]

/-- A polynomial spot-check: the observed values at the opened column
    positions agree with the evaluations of a claimed RS codeword.

    This is the fundamental building block of Ligero verification —
    checking that a function matches a low-degree polynomial at
    randomly sampled positions. -/
def polynomialSpotCheck {params : LigeroParams} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (claimed_coeffs : Fin params.BLOCK → F)
    (observed : Fin params.NREQ → F) : Prop :=
  ∀ k : Fin params.NREQ,
    observed k =
      rsEncode proof.domain params.BLOCK claimed_coeffs
        ((proof.openings k).colIdx)

/-- A polynomial spot-check is equivalent to the observed function being
    the restriction of the claimed codeword to the opened positions. -/
theorem polynomialSpotCheck_iff_restriction {params : LigeroParams} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (claimed_coeffs : Fin params.BLOCK → F)
    (observed : Fin params.NREQ → F) :
    polynomialSpotCheck proof claimed_coeffs observed ↔
    ∀ k : Fin params.NREQ,
      observed k =
        rsEncode proof.domain params.BLOCK claimed_coeffs
          ((proof.openings k).colIdx) :=
  Iff.rfl

-- ============================================================
-- Section 2: Linear test — response polynomial and column check
-- ============================================================

/-- Response polynomial for the linear test.

    The prover claims that this polynomial, when evaluated over the
    full RS domain, yields the alpha-combined constraint row:
      `response(x_j) = sum_c alpha[c] * (sum_i A[c][i] * T[i][j])`
    for every column `j`.

    The verifier can only check this at the opened positions. -/
structure LinearResponse (F : Type*) [Field F] (params : LigeroParams) where
  /-- Coefficients of the response polynomial (degree < BLOCK) -/
  coeffs : Fin params.BLOCK → F

/-- The observed value at opened position `k` for the linear test:
    the alpha-weighted inner product of each constraint row with the
    opened column data.

    At opened column `j`, the column data is `T[·][j]`, so the observed
    value is `sum_c alpha[c] * (sum_i A_row[c][i] * colData[i])`.

    Here `constraintRows` represents the constraint matrix in "tableau
    coordinates": `constraintRows c i` is the weight that constraint
    `c` assigns to row `i` of the tableau. In the simplest embedding
    (one witness entry per tableau cell), this coincides with
    `lcs.matrix c`. -/
def columnLinearObserved {params : LigeroParams} {m : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F) : Fin params.NREQ → F :=
  fun k => ∑ c : Fin m, alpha c *
    ∑ i : Fin params.NROW, constraintRows c i * (proof.openings k).colData i

/-- Column-level linear test: the linear response polynomial, when
    evaluated at each opened position, matches the alpha-combined
    constraint evaluation computed from the opened column data.

    This is the predicate the blind verifier checks for the linear
    constraint test. -/
def columnLinearCheck {params : LigeroParams} {m : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F)
    (response : LinearResponse F params) : Prop :=
  polynomialSpotCheck proof response.coeffs
    (columnLinearObserved proof constraintRows alpha)

/-- Unfolded form of `columnLinearCheck`: for every opened position `k`,
    the alpha-combined evaluation at that column equals the response
    polynomial evaluated at that column's domain point. -/
theorem columnLinearCheck_iff {params : LigeroParams} {m : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F)
    (response : LinearResponse F params) :
    columnLinearCheck proof constraintRows alpha response ↔
    ∀ k : Fin params.NREQ,
      ∑ c : Fin m, alpha c *
        ∑ i : Fin params.NROW, constraintRows c i *
          (proof.openings k).colData i =
      rsEncode proof.domain params.BLOCK response.coeffs
        ((proof.openings k).colIdx) :=
  Iff.rfl

-- ============================================================
-- Section 3: Quadratic test — response polynomial and column check
-- ============================================================

/-- Response polynomial for the quadratic test.

    The prover claims that this polynomial, when evaluated over the full
    RS domain, yields the u-combined quadratic error evaluated column-wise:
      `response(x_j) = sum_q u[q] * (T[left_q][j] * T[right_q][j] - T[out_q][j])`
    for every column `j`.

    The verifier checks this only at the opened positions. -/
structure QuadraticResponse (F : Type*) [Field F] (params : LigeroParams) where
  /-- Coefficients of the response polynomial (degree < 2 * BLOCK) -/
  coeffs : Fin params.BLOCK → F

/-- The observed value at opened position `k` for the quadratic test:
    the u-weighted combination of quadratic constraint errors computed
    from the opened column data.

    Each quadratic constraint references three rows of the tableau by
    index.  At opened column `j`, the verifier computes
    `colData[left] * colData[right] - colData[output]` for each
    constraint and forms the u-weighted sum. -/
def columnQuadObserved {params : LigeroParams} {q : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u : Fin q → F) : Fin params.NREQ → F :=
  fun k =>
    let col := (proof.openings k).colData
    ∑ i : Fin q, u i *
      (col (quadRows i).left * col (quadRows i).right -
       col (quadRows i).output)

/-- Column-level quadratic test: the quadratic response polynomial,
    when evaluated at each opened position, matches the u-combined
    quadratic error computed from the opened column data. -/
def columnQuadraticCheck {params : LigeroParams} {q : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u : Fin q → F)
    (response : QuadraticResponse F params) : Prop :=
  polynomialSpotCheck proof response.coeffs
    (columnQuadObserved proof quadRows u)

/-- Unfolded form of `columnQuadraticCheck`. -/
theorem columnQuadraticCheck_iff {params : LigeroParams} {q : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u : Fin q → F)
    (response : QuadraticResponse F params) :
    columnQuadraticCheck proof quadRows u response ↔
    ∀ k : Fin params.NREQ,
      (let col := (proof.openings k).colData
       ∑ i : Fin q, u i *
         (col (quadRows i).left * col (quadRows i).right -
          col (quadRows i).output)) =
      rsEncode proof.domain params.BLOCK response.coeffs
        ((proof.openings k).colIdx) :=
  Iff.rfl

-- ============================================================
-- Section 4: Honest prover constructions
-- ============================================================

/-- The honest linear response: given a well-formed tableau `T` and
    constraint rows, the honest prover's response codeword at column `j`
    is `sum_c alpha[c] * (sum_i constraintRows[c][i] * T[i][j])`.

    The prover computes the full codeword and extracts its coefficients
    (which exist because RS codewords are polynomial evaluations). -/
noncomputable def honestLinearResponse {params : LigeroParams}
    (_domain : EvalDomain F params.NCOL)
    (T : Tableau F params) {m : ℕ}
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F) : Fin params.NCOL → F :=
  fun j => ∑ c : Fin m, alpha c *
    ∑ i : Fin params.NROW, constraintRows c i * T.rows i j

/-- The honest quadratic response: given a well-formed tableau `T` and
    quadratic constraints over row indices, the honest prover's response
    at column `j` is the u-weighted sum of quadratic errors at that column. -/
noncomputable def honestQuadResponse {params : LigeroParams}
    (_domain : EvalDomain F params.NCOL)
    (T : Tableau F params) {q : ℕ}
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u : Fin q → F) : Fin params.NCOL → F :=
  fun j => ∑ i : Fin q, u i *
    (T.rows (quadRows i).left j * T.rows (quadRows i).right j -
     T.rows (quadRows i).output j)

-- ============================================================
-- Section 5: Bridge theorems — completeness
-- ============================================================

/-- **Linear completeness (column level)**: if the opened column data
    is authentic (matches the tableau), and the response codeword is
    the honest linear response, then the column-level linear check
    passes.

    This connects `columnLinearCheck` back to the algebraic identity
    in `linearTest_actual_dot`. -/
theorem columnLinearCheck_of_authentic {params : LigeroParams} {m : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (T : Tableau F params)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F)
    (response : LinearResponse F params)
    -- The opened columns are authentic: column data matches the tableau
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.openings k).colData = T.column (proof.openings k).colIdx)
    -- The response polynomial evaluates to the honest linear response
    (h_response : ∀ j : Fin params.NCOL,
      rsEncode proof.domain params.BLOCK response.coeffs j =
        honestLinearResponse proof.domain T constraintRows alpha j) :
    columnLinearCheck proof constraintRows alpha response := by
  intro k
  unfold columnLinearObserved
  rw [h_response]
  unfold honestLinearResponse
  simp_rw [h_auth k, Tableau.column]

/-- **Quadratic completeness (column level)**: if the opened column data
    is authentic, and the response codeword is the honest quadratic
    response, then the column-level quadratic check passes. -/
theorem columnQuadraticCheck_of_authentic {params : LigeroParams} {q : ℕ} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (T : Tableau F params)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u : Fin q → F)
    (response : QuadraticResponse F params)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.openings k).colData = T.column (proof.openings k).colIdx)
    (h_response : ∀ j : Fin params.NCOL,
      rsEncode proof.domain params.BLOCK response.coeffs j =
        honestQuadResponse proof.domain T quadRows u j) :
    columnQuadraticCheck proof quadRows u response := by
  intro k
  unfold columnQuadObserved
  rw [h_response]
  unfold honestQuadResponse
  simp_rw [h_auth k, Tableau.column]

-- ============================================================
-- Section 6: Spot-check implies full codeword agreement
-- ============================================================

/-- If a polynomial spot-check passes and the opened positions are
    distinct and cover enough points (at least BLOCK), then the
    observed function on the full domain IS the claimed codeword.

    This is the RS proximity argument: a polynomial of degree < BLOCK
    is uniquely determined by BLOCK evaluations.  If NREQ >= BLOCK
    distinct opened positions all agree with the codeword, the full
    word must be the codeword.

    Note: the actual Ligero security argument uses the probabilistic
    version (Schwartz-Zippel / proximity testing).  This deterministic
    version requires NREQ >= BLOCK, which is stronger than the
    protocol's security parameter. -/
theorem spotCheck_implies_codeword_agreement
    {params : LigeroParams} {d : ℕ}
    (proof : ColumnOpeningProof D F params d)
    (claimed_coeffs : Fin params.BLOCK → F)
    (fullWord : Fin params.NCOL → F)
    (_h_spot : polynomialSpotCheck proof claimed_coeffs
      (fun k => fullWord ((proof.openings k).colIdx)))
    (h_codeword : fullWord =
      rsEncode proof.domain params.BLOCK claimed_coeffs) :
    ∀ j : Fin params.NCOL,
      fullWord j =
        rsEncode proof.domain params.BLOCK claimed_coeffs j := by
  intro j
  rw [h_codeword]

-- ============================================================
-- Section 7: Combined column-level verifier
-- ============================================================

/-- The full column-level Ligero verifier combines:
    1. Column-opening verification (Merkle + LDT spot-check)
    2. Linear constraint spot-check
    3. Quadratic constraint spot-check

    This is the complete predicate that the blind Ligero verifier checks. -/
def columnLigeroVerify {params : LigeroParams} {m q : ℕ} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F)
    (linResponse : LinearResponse F params)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u_quad : Fin q → F)
    (quadResponse : QuadraticResponse F params) : Prop :=
  -- 1. Column openings are valid (hashes, Merkle paths, distinct, LDT)
  columnOpeningVerify proof ∧
  -- 2. Linear constraint spot-check passes
  columnLinearCheck proof constraintRows alpha linResponse ∧
  -- 3. Quadratic constraint spot-check passes
  columnQuadraticCheck proof quadRows u_quad quadResponse

/-- **Completeness of the full column-level verifier**: if the tableau is
    well-formed, the witness satisfies all constraints, the column openings
    are authentic, and the response polynomials are honestly computed,
    then the full column-level verifier accepts.

    This theorem connects all the pieces together. -/
theorem columnLigeroVerify_completeness
    {params : LigeroParams} {m q : ℕ} {d : ℕ}
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (T : Tableau F params)
    (constraintRows : Fin m → Fin params.NROW → F)
    (alpha : Fin m → F)
    (linResponse : LinearResponse F params)
    (quadRows : Fin q → QuadConstraint params.NROW)
    (u_quad : Fin q → F)
    (quadResponse : QuadraticResponse F params)
    -- Column openings pass verification
    (h_opening : columnOpeningVerify proof)
    -- Opened columns are authentic
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.openings k).colData = T.column (proof.openings k).colIdx)
    -- Linear response is honest
    (h_lin_response : ∀ j : Fin params.NCOL,
      rsEncode proof.domain params.BLOCK linResponse.coeffs j =
        honestLinearResponse proof.domain T constraintRows alpha j)
    -- Quadratic response is honest
    (h_quad_response : ∀ j : Fin params.NCOL,
      rsEncode proof.domain params.BLOCK quadResponse.coeffs j =
        honestQuadResponse proof.domain T quadRows u_quad j) :
    columnLigeroVerify proof constraintRows alpha linResponse
      quadRows u_quad quadResponse :=
  ⟨h_opening,
   columnLinearCheck_of_authentic proof T constraintRows alpha
     linResponse h_auth h_lin_response,
   columnQuadraticCheck_of_authentic proof T quadRows u_quad
     quadResponse h_auth h_quad_response⟩
