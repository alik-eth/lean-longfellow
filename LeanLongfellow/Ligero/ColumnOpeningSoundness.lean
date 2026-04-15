import LeanLongfellow.Ligero.ColumnOpening
import LeanLongfellow.Ligero.Tests.LowDegree
import LeanLongfellow.Ligero.ReedSolomon.Proximity

/-! # Column-Opening LDT Soundness

This file connects the column-opening spot-check (defined in `ColumnOpening.lean`)
to the existing Reed-Solomon proximity bounds (in `ReedSolomon/Proximity.lean`).

## Main results

1. **`column_ldt_consistency`**: If the column-opening verifier's LDT check passes
   and the opened column data matches the committed tableau, then the claimed
   combined-row codeword agrees with the TRUE combined row at all opened positions.

2. **`column_ldt_agreement_bound`**: If the claimed codeword differs from the true
   combined row (and both are RS codewords), they agree on at most `BLOCK - 1`
   positions. This follows from `rs_agreement_bound`.

3. **`column_ldt_detection_probability`**: The number of `NREQ`-tuples of positions
   where the claimed codeword and true combined row agree everywhere is bounded
   by `(BLOCK - 1) ^ NREQ`. This follows from `proximity_detection_multi_bad_bound`.

## Overview

The column-opening verifier checks that `∑_i u[i] * colData[k][i] = rsEncode(coeffs, colIdx k)`.
If the opened column data is authentic (`colData[k] = tableau.column(colIdx k)`), then the
left-hand side equals `combinedRow(tableau, u, colIdx k)` by definition. This means the
claimed codeword agrees with the true combined row at every opened position.

If the claimed codeword differs from the true combined row, the RS distance bound limits
how many positions can agree, giving a soundness bound on the LDT.
-/

set_option autoImplicit false

open Finset in

-- ============================================================
-- Section 1: Consistency — LDT check implies pointwise agreement
-- ============================================================

/-- **Column LDT consistency**: If the column-opening verifier's LDT check passes
    and the opened column data matches the committed tableau, then the claimed
    combined-row codeword agrees with the true combined row at all opened positions.

    This is the main bridge between the "blind" column-opening verifier and
    the full LDT: the verifier's spot-check is equivalent to checking that
    the claimed codeword matches the actual combined row at the opened positions. -/
theorem column_ldt_consistency {params : LigeroParams} {d : ℕ}
    {D : Type*} [MerkleHash D] {F : Type*} [Field F]
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (tableau : Tableau F params)
    (hverify : columnOpeningVerify proof)
    -- Opened data matches committed tableau
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.openings k).colData = tableau.column (proof.openings k).colIdx) :
    -- The claimed codeword agrees with the true combined row at opened positions
    ∀ k : Fin params.NREQ,
      rsEncode proof.domain params.BLOCK proof.combinedRowCoeffs ((proof.openings k).colIdx) =
      combinedRow tableau proof.ldt_u ((proof.openings k).colIdx) := by
  intro k
  -- Extract the LDT spot-check from the verifier predicate
  obtain ⟨_, _, _, h_ldt⟩ := hverify
  -- The LDT check gives: ∑_i u[i] * colData[k][i] = rsEncode ... (colIdx k)
  have h_spot := h_ldt k
  -- By h_auth, colData[k] = tableau.column (colIdx k)
  have h_col := h_auth k
  -- Rewrite the LDT check using the authenticity of the column data
  rw [h_col] at h_spot
  -- Now h_spot : ∑ i, u[i] * tableau.column (colIdx k) i = rsEncode ... (colIdx k)
  -- The left side is exactly combinedRow tableau u (colIdx k)
  -- combinedRow T u col = ∑ i, u i * T.rows i col
  -- tableau.column j i = T.rows i j
  -- So ∑ i, u i * tableau.column (colIdx k) i = ∑ i, u i * T.rows i (colIdx k)
  --    = combinedRow tableau u (colIdx k)
  -- h_spot has the form: ∑ i, u i * (tableau.column j) i = rsEncode ...
  -- We need: rsEncode ... = ∑ i, u i * tableau.rows i j
  -- These are equal since tableau.column j i = tableau.rows i j
  have h_unfold : ∀ i, tableau.column (proof.openings k).colIdx i =
      tableau.rows i ((proof.openings k).colIdx) := fun _ => rfl
  simp only [h_unfold] at h_spot
  exact h_spot.symm

-- ============================================================
-- Section 2: Agreement bound — distinct codewords agree on few positions
-- ============================================================

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Column LDT agreement bound**: If the claimed codeword differs from the
    true combined row, and the true combined row is itself an RS codeword
    (which it is when all tableau rows are codewords), then they agree on
    at most `BLOCK - 1` positions.

    This follows directly from `rs_agreement_bound`: the claimed codeword is
    `rsEncode domain BLOCK claimed_coeffs` (a codeword by construction), and
    the true combined row is a codeword by hypothesis. Two distinct codewords
    of degree `< BLOCK` over an `NCOL`-point domain agree on at most
    `BLOCK - 1` positions. -/
theorem column_ldt_agreement_bound {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (claimed_coeffs : Fin params.BLOCK → F)
    (trueCombined : Fin params.NCOL → F)
    (h_diff : rsEncode domain params.BLOCK claimed_coeffs ≠ trueCombined)
    (h_true_cw : isRSCodeword domain params.BLOCK trueCombined) :
    (Finset.univ.filter fun j : Fin params.NCOL =>
      rsEncode domain params.BLOCK claimed_coeffs j = trueCombined j).card ≤ params.BLOCK - 1 :=
  rs_agreement_bound domain params.BLOCK (le_of_lt params.h_block_lt)
    (rsEncode domain params.BLOCK claimed_coeffs) trueCombined
    ⟨claimed_coeffs, rfl⟩ h_true_cw h_diff

-- ============================================================
-- Section 3: Detection probability — multi-position detection bound
-- ============================================================

/-- **Column LDT detection probability**: If the claimed codeword differs from
    the true combined row (and both are codewords), then the number of
    `NREQ`-tuples of positions where they agree at ALL positions is bounded
    by `(BLOCK - 1) ^ NREQ`.

    This follows from `proximity_detection_multi_bad_bound`: the agreement set
    has at most `BLOCK - 1` elements, so the number of `t`-tuples landing
    entirely in the agreement set is at most `(BLOCK - 1) ^ t`. -/
theorem column_ldt_detection_probability {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (claimed_coeffs : Fin params.BLOCK → F)
    (trueCombined : Fin params.NCOL → F)
    (h_diff : rsEncode domain params.BLOCK claimed_coeffs ≠ trueCombined)
    (h_true_cw : isRSCodeword domain params.BLOCK trueCombined) :
    (Finset.univ.filter fun positions : Fin params.NREQ → Fin params.NCOL =>
      ∀ k, rsEncode domain params.BLOCK claimed_coeffs (positions k) =
        trueCombined (positions k)).card
    ≤ (params.BLOCK - 1) ^ params.NREQ :=
  proximity_detection_multi_bad_bound domain params.BLOCK (le_of_lt params.h_block_lt)
    (rsEncode domain params.BLOCK claimed_coeffs) trueCombined
    ⟨claimed_coeffs, rfl⟩ h_true_cw h_diff params.NREQ

-- ============================================================
-- Section 4: Combined soundness — end-to-end column-opening LDT soundness
-- ============================================================

omit [DecidableEq F] in
/-- **Column-opening LDT soundness (positions)**: If the column-opening verifier
    accepts and the opened data is authentic, then every opened position falls
    in the agreement set between the claimed codeword and the true combined row.

    When combined with `column_ldt_soundness_agreement_bound` (which shows the
    agreement set has at most `BLOCK - 1` elements), this constrains the
    positions that could have been opened: the prover can only cheat if all
    `NREQ` opened positions happen to fall among at most `BLOCK - 1` "lucky"
    positions out of `NCOL` total. -/
theorem column_ldt_soundness_positions {params : LigeroParams} {d : ℕ}
    {D : Type*} [MerkleHash D]
    [ColumnHash D F params.NROW]
    (proof : ColumnOpeningProof D F params d)
    (tableau : Tableau F params)
    (hverify : columnOpeningVerify proof)
    (h_auth : ∀ k : Fin params.NREQ,
      (proof.openings k).colData = tableau.column (proof.openings k).colIdx) :
    -- Every opened position falls in the agreement set
    ∀ k : Fin params.NREQ,
      rsEncode proof.domain params.BLOCK proof.combinedRowCoeffs ((proof.openings k).colIdx) =
      combinedRow tableau proof.ldt_u ((proof.openings k).colIdx) := by
  intro k
  exact column_ldt_consistency proof tableau hverify h_auth k

/-- **Column-opening LDT soundness (agreement bound)**: Under the same
    conditions as `column_ldt_soundness_positions`, the set of column positions
    where the claimed codeword agrees with the true combined row has at most
    `BLOCK - 1` elements. Combined with the fact that all `NREQ` opened
    positions must be in this agreement set, this gives the soundness bound:
    the prover can only cheat if all `NREQ` opened positions happen to fall
    among at most `BLOCK - 1` "lucky" positions out of `NCOL` total. -/
theorem column_ldt_soundness_agreement_bound {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (tableau : Tableau F params)
    (u : Fin params.NROW → F)
    (claimed_coeffs : Fin params.BLOCK → F)
    (h_wf : tableauWellFormed domain tableau)
    (h_diff : rsEncode domain params.BLOCK claimed_coeffs ≠ combinedRow tableau u) :
    (Finset.univ.filter fun j : Fin params.NCOL =>
      rsEncode domain params.BLOCK claimed_coeffs j =
      combinedRow tableau u j).card ≤ params.BLOCK - 1 :=
  column_ldt_agreement_bound domain claimed_coeffs (combinedRow tableau u) h_diff
    (combined_is_codeword_of_wf domain tableau u h_wf)
