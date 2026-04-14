import LeanLongfellow.Ligero.ReedSolomon.Defs

/-! # Ligero Tableau Structure

The Ligero tableau is an NROW × NCOL matrix where each row is a
Reed-Solomon codeword.  This file defines the parameters, the
tableau type, well-formedness, and witness embedding.
-/

/-- Parameters for the Ligero scheme. -/
structure LigeroParams where
  NROW : ℕ       -- number of rows
  NCOL : ℕ       -- number of columns (evaluation domain size)
  BLOCK : ℕ      -- message length = degree bound for RS
  NREQ : ℕ       -- number of columns opened (security parameter)
  h_block_lt : BLOCK < NCOL
  h_nreq_le : NREQ ≤ NCOL - BLOCK

/-- The Ligero tableau: an NROW × NCOL matrix over a field `F`. -/
structure Tableau (F : Type*) [Field F] (params : LigeroParams) where
  rows : Fin params.NROW → Fin params.NCOL → F

/-- Every row of the tableau is a valid Reed-Solomon codeword. -/
def tableauWellFormed {F : Type*} [Field F] {params : LigeroParams}
    (domain : EvalDomain F params.NCOL) (T : Tableau F params) : Prop :=
  ∀ i : Fin params.NROW, isRSCodeword domain params.BLOCK (T.rows i)

/-- The first `BLOCK` entries of row `i` — the "message" portion. -/
def rowMessage {F : Type*} [Field F] {params : LigeroParams}
    (T : Tableau F params) (i : Fin params.NROW) : Fin params.BLOCK → F :=
  fun j => T.rows i ⟨j.val, by have := params.h_block_lt; omega⟩

/-- The witness `w` is correctly embedded in the tableau starting at
    row `IW`, using `WR` columns per row for witness data. -/
def witnessEmbedded {F : Type*} [Field F] {params : LigeroParams} {n : ℕ}
    (T : Tableau F params) (w : Fin n → F)
    (IW : ℕ) (WR : ℕ) (NREQ : ℕ)
    (_h_block : params.BLOCK = NREQ + WR) : Prop :=
  ∀ (widx : Fin n),
    let row_idx := widx.val / WR
    let col_offset := widx.val % WR
    ∃ (hr : IW + row_idx < params.NROW)
      (hc : NREQ + col_offset < params.NCOL),
      T.rows ⟨IW + row_idx, hr⟩ ⟨NREQ + col_offset, hc⟩ = w widx
