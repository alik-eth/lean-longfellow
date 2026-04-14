import LeanLongfellow.Ligero.Tableau
import LeanLongfellow.Ligero.ReedSolomon.Defs
import LeanLongfellow.Ligero.ReedSolomon.Distance
import LeanLongfellow.Ligero.ReedSolomon.Proximity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs

open Finset Polynomial

/-! # Ligero Low-Degree Test

The low-degree test (LDT) checks that every row of the Ligero tableau is a
valid Reed-Solomon codeword.  The verifier:

1. Samples random coefficients `u[0..NROW-1]`.
2. Forms the combined row: `combined[col] = ∑ u[i] · T[i][col]`.
3. Checks whether the combined row is itself a valid RS codeword (either by
   re-encoding or by spot-checking at opened positions).

**Completeness:** If all rows are codewords, the combined row is a codeword
(linear combination of codewords), so the test always accepts.

**Soundness (deterministic):** If the combined row is NOT a codeword, it
disagrees with every codeword on at least one position.  Opening `NREQ`
random positions catches this with high probability.

## Main results

- `combinedRow`: the random linear combination of tableau rows.
- `combinedRowIsCodeword`: predicate that the combined row is a valid codeword.
- `combined_is_codeword_of_wf`: completeness — if all rows are codewords,
  the combined row is a codeword.
- `lowDegreeTestAccepts`: the verifier's acceptance predicate.
- `lowDegreeTest_completeness`: if all rows are codewords, the LDT accepts.
- `lowDegreeTest_soundness_hamming`: if the combined row is not a codeword,
  it disagrees with any codeword on at least one position.
-/

variable {F : Type*} [Field F]

/-! ### Combined row -/

/-- The combined row: the random linear combination of tableau rows. -/
def combinedRow {params : LigeroParams}
    (T : Tableau F params) (u : Fin params.NROW → F) :
    Fin params.NCOL → F :=
  fun col => ∑ i : Fin params.NROW, u i * T.rows i col

/-- The combined row is itself a valid RS codeword. -/
def combinedRowIsCodeword {params : LigeroParams}
    (domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F) : Prop :=
  isRSCodeword domain params.BLOCK (combinedRow T u)

/-! ### Linearity of RS encoding -/

/-- RS encoding is linear: `rsEncode(∑ u[i] · coeffsᵢ) = ∑ u[i] · rsEncode(coeffsᵢ)`.
    This is the key algebraic fact: evaluation is linear. -/
theorem rsEncode_linear_combination {N k : ℕ} {m : ℕ}
    (domain : EvalDomain F N)
    (coeffs_family : Fin m → Fin k → F)
    (u : Fin m → F) :
    rsEncode domain k (fun j => ∑ i : Fin m, u i * coeffs_family i j) =
    fun col => ∑ i : Fin m, u i * rsEncode domain k (coeffs_family i) col := by
  funext col
  simp only [rsEncode]
  simp only [map_sum, map_mul, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  ring

/-! ### Completeness -/

/-- If all rows are codewords, the combined row is also a codeword.
    Proof: each row is `rsEncode domain BLOCK coeffsᵢ`.  The combined row
    is `rsEncode domain BLOCK (∑ u[i] · coeffsᵢ)` by linearity of evaluation. -/
theorem combined_is_codeword_of_wf {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (h_wf : tableauWellFormed domain T) :
    combinedRowIsCodeword domain T u := by
  unfold combinedRowIsCodeword combinedRow isRSCodeword
  -- Each row is a codeword: extract the coefficients
  have h_coeffs : ∀ i, ∃ coeffs : Fin params.BLOCK → F,
      T.rows i = rsEncode domain params.BLOCK coeffs := h_wf
  choose coeffs_family h_eq using h_coeffs
  -- The combined row equals rsEncode of the combined coefficients
  use fun j => ∑ i : Fin params.NROW, u i * coeffs_family i j
  funext col
  simp only [rsEncode_linear_combination]
  congr 1; ext i
  congr 1
  exact congrFun (h_eq i) col

/-! ### Low-degree test acceptance predicate -/

/-- The low-degree test: combine rows with random `u`, and check that the
    combined row agrees with some codeword at the opened positions.

    This models the verifier's check: the prover commits to the tableau,
    the verifier picks random `u` and `opened`, and the prover reveals the
    opened columns.  The verifier forms the combined row at those positions
    and checks whether it is consistent with a low-degree polynomial. -/
def lowDegreeTestAccepts {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL) : Prop :=
  -- The combined row agrees with some codeword at all opened positions
  ∃ cw : Fin params.NCOL → F,
    isRSCodeword domain params.BLOCK cw ∧
    ∀ j : Fin params.NREQ, cw (opened j) = combinedRow T u (opened j)

/-- If the combined row IS a codeword, the LDT accepts (with the combined row
    itself as witness). -/
theorem lowDegreeTest_accepts_of_codeword {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL)
    (h_cw : combinedRowIsCodeword domain T u) :
    lowDegreeTestAccepts domain T u opened :=
  ⟨combinedRow T u, h_cw, fun _ => rfl⟩

/-- **Completeness**: If all rows are codewords, the low-degree test always
    accepts regardless of the choice of `u` and `opened`. -/
theorem lowDegreeTest_completeness {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL)
    (h_wf : tableauWellFormed domain T) :
    lowDegreeTestAccepts domain T u opened :=
  lowDegreeTest_accepts_of_codeword domain T u opened
    (combined_is_codeword_of_wf domain T u h_wf)

/-! ### Alternative: direct codeword check -/

/-- A stronger (and simpler) formulation of the LDT: the verifier directly
    checks that the combined row is a codeword.  If accepted, the combined
    row is a codeword by definition.

    This is the "ideal" LDT that a polynomial commitment scheme would use. -/
def lowDegreeTestIdeal {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F) : Prop :=
  combinedRowIsCodeword domain T u

/-- Completeness of the ideal LDT. -/
theorem lowDegreeTestIdeal_completeness {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (h_wf : tableauWellFormed domain T) :
    lowDegreeTestIdeal domain T u :=
  combined_is_codeword_of_wf domain T u h_wf

/-- The ideal LDT implies the standard LDT for any choice of opened positions. -/
theorem lowDegreeTestIdeal_implies_accepts {params : LigeroParams}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL)
    (h : lowDegreeTestIdeal domain T u) :
    lowDegreeTestAccepts domain T u opened :=
  lowDegreeTest_accepts_of_codeword domain T u opened h

/-! ### Soundness: non-codeword detection via proximity -/

/-- If the combined row is NOT a codeword, then it disagrees with every
    codeword on at least one position.  In particular, the LDT cannot accept
    with a codeword witness that matches the combined row everywhere. -/
theorem lowDegreeTest_codeword_witness_ne {params : LigeroParams}
    (_domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F)
    (h_not_cw : ¬ combinedRowIsCodeword _domain T u) :
    ∀ cw : Fin params.NCOL → F,
      isRSCodeword _domain params.BLOCK cw →
      cw ≠ combinedRow T u := by
  intro cw h_cw h_eq
  apply h_not_cw
  unfold combinedRowIsCodeword
  rw [show combinedRow T u = cw from h_eq.symm]
  exact h_cw

/-- **Soundness (existence of disagreement)**: If the combined row is NOT a
    codeword, then for any codeword, there exists a position where they
    disagree. -/
theorem combined_not_codeword_differs {params : LigeroParams} [DecidableEq F]
    (domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F)
    (h_not_cw : ¬ combinedRowIsCodeword domain T u)
    (cw : Fin params.NCOL → F)
    (h_cw : isRSCodeword domain params.BLOCK cw) :
    ∃ i : Fin params.NCOL, combinedRow T u i ≠ cw i :=
  non_codeword_differs domain params.BLOCK (combinedRow T u) h_not_cw cw h_cw

/-- **Soundness (Hamming distance)**: If the combined row is NOT a codeword,
    the Hamming distance to any codeword is at least 1. -/
theorem lowDegreeTest_soundness_hamming {params : LigeroParams} [DecidableEq F]
    (domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F)
    (h_not_cw : ¬ combinedRowIsCodeword domain T u)
    (cw : Fin params.NCOL → F)
    (h_cw : isRSCodeword domain params.BLOCK cw) :
    0 < (hammingDiffSet (combinedRow T u) cw).card :=
  non_codeword_hamming_pos domain params.BLOCK (combinedRow T u) h_not_cw cw h_cw

/-- **Soundness (agreement bound for codeword witnesses)**: If the combined row
    is NOT a codeword, then for any codeword `cw`, the set of positions where
    they agree has strictly fewer than `NCOL` elements.

    This means that any tuple of random positions will, with nonzero probability,
    hit a disagreement point. -/
theorem combined_not_codeword_agree_lt {params : LigeroParams} [DecidableEq F]
    (domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F)
    (h_not_cw : ¬ combinedRowIsCodeword domain T u)
    (cw : Fin params.NCOL → F)
    (h_cw : isRSCodeword domain params.BLOCK cw) :
    (Finset.univ.filter (fun i => combinedRow T u i = cw i)).card < params.NCOL :=
  non_codeword_agree_card_lt domain params.BLOCK (combinedRow T u) h_not_cw cw h_cw

/-- **Key soundness fact**: If the combined row is not a codeword and the opened
    positions include at least one position where `cw` and the combined row
    differ, the test rejects with that `cw` witness. -/
theorem lowDegreeTest_rejects_if_disagree_opened {params : LigeroParams}
    (T : Tableau F params)
    (u : Fin params.NROW → F)
    (opened : Fin params.NREQ → Fin params.NCOL)
    (cw : Fin params.NCOL → F)
    (h_disagree : ∃ j : Fin params.NREQ,
        cw (opened j) ≠ combinedRow T u (opened j)) :
    ¬ (∀ j : Fin params.NREQ, cw (opened j) = combinedRow T u (opened j)) := by
  intro h_all
  obtain ⟨j, hj⟩ := h_disagree
  exact hj (h_all j)

/-- **Soundness (multi-position detection)**: If the combined row is NOT a
    codeword, then for any codeword `cw`, a `t`-tuple of positions that ALL
    agree with `cw` must come from the agreement set, which has fewer than
    `NCOL` elements.  The number of such "bad" tuples is at most
    `agree.card ^ t`, which is strictly less than `NCOL ^ t` when `t > 0`. -/
theorem lowDegreeTest_multi_detection {params : LigeroParams} [DecidableEq F]
    (domain : EvalDomain F params.NCOL) (T : Tableau F params)
    (u : Fin params.NROW → F)
    (h_not_cw : ¬ combinedRowIsCodeword domain T u)
    (cw : Fin params.NCOL → F)
    (h_cw : isRSCodeword domain params.BLOCK cw)
    (t : ℕ) (ht : 0 < t) :
    (Finset.univ.filter (fun pos : Fin t → Fin params.NCOL =>
      ∀ j : Fin t, combinedRow T u (pos j) = cw (pos j))).card <
    params.NCOL ^ t := by
  -- Let A = agreement set = {i | combinedRow T u i = cw i}
  set A := Finset.univ.filter (fun i : Fin params.NCOL =>
    combinedRow T u i = cw i) with hA_def
  have hA_lt : A.card < params.NCOL :=
    combined_not_codeword_agree_lt domain T u h_not_cw cw h_cw
  -- The bad tuples are exactly functions Fin t → A (lifted to Fin t → Fin NCOL)
  -- Step 1: The filter set is contained in the set of functions with range ⊆ A
  have h_sub : Finset.univ.filter (fun pos : Fin t → Fin params.NCOL =>
      ∀ j : Fin t, combinedRow T u (pos j) = cw (pos j)) ⊆
      Fintype.piFinset (fun _ : Fin t => A) := by
    intro pos hpos
    rw [Finset.mem_filter] at hpos
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hpos.2 j⟩
  -- Step 2: card of piFinset = A.card ^ t
  have h_pi_card : (Fintype.piFinset (fun _ : Fin t => A)).card = A.card ^ t := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const]
  -- Step 3: chain the inequalities
  calc (Finset.univ.filter _).card
      ≤ (Fintype.piFinset (fun _ : Fin t => A)).card := Finset.card_le_card h_sub
    _ = A.card ^ t := h_pi_card
    _ < params.NCOL ^ t := Nat.pow_lt_pow_left hA_lt (by omega)
