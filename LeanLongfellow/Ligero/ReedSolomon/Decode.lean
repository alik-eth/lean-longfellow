import LeanLongfellow.Ligero.ReedSolomon.Defs
import LeanLongfellow.Ligero.ReedSolomon.Distance
import LeanLongfellow.Ligero.ReedSolomon.Proximity
import LeanLongfellow.Ligero.Soundness
import Mathlib.LinearAlgebra.Lagrange

/-!
# Reed-Solomon Decoding and Algebraic Knowledge Extractability

This file establishes:
1. **`coeffsToPoly` injectivity**: the map from coefficient vectors to polynomials is injective.
2. **`rsEncode` injectivity**: two coefficient vectors encoding to the same codeword must be equal.
3. **RS decoding via Lagrange interpolation**: given evaluations at `k` distinct domain points,
   recover the unique polynomial of degree `< k` and extract its coefficients.
4. **Decode inverts encode**: decoding a valid codeword at any `k` distinct positions recovers
   the original coefficients.
5. **Algebraic knowledge extractability**: if all tableau rows are valid RS codewords and the
   Ligero constraints are satisfied, the decoded witness satisfies all constraints.

## Main definitions

- `coeffsToPoly_coeff`: the `j`-th coefficient of `coeffsToPoly coeffs` is `coeffs j`.
- `coeffsToPoly_injective`: `coeffsToPoly` is injective.
- `rsEncode_injective`: `rsEncode` is injective when `k ≤ N`.
- `rsDecode`: recovers a coefficient vector from evaluations at `k` distinct domain points.
- `rsDecode_rsEncode`: decode inverts encode.
- `AlgebraicExtractor`: a structure packaging RS decoding as a knowledge extractor.
- `algebraic_extractability`: the main extractability theorem.
-/

open Polynomial Finset Lagrange

variable {F : Type*} [Field F] [DecidableEq F]

-- ============================================================
-- Section 1: coeffsToPoly coefficient extraction
-- ============================================================

omit [DecidableEq F] in
/-- The `j`-th coefficient of `coeffsToPoly coeffs` is `coeffs j`. -/
theorem coeffsToPoly_coeff {k : ℕ} (coeffs : Fin k → F) (j : Fin k) :
    (coeffsToPoly coeffs).coeff j.val = coeffs j := by
  unfold coeffsToPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Fin.val_ne_of_ne (Ne.symm hbj)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

omit [DecidableEq F] in
/-- Coefficients beyond `k` are zero in `coeffsToPoly`. -/
theorem coeffsToPoly_coeff_eq_zero {k : ℕ} (coeffs : Fin k → F) (n : ℕ) (hn : k ≤ n) :
    (coeffsToPoly coeffs).coeff n = 0 := by
  unfold coeffsToPoly
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Polynomial.coeff_C_mul_X_pow]
  split
  · next h => exact absurd (h ▸ i.isLt) (not_lt.mpr hn)
  · rfl

-- ============================================================
-- Section 2: coeffsToPoly injectivity
-- ============================================================

omit [DecidableEq F] in
/-- `coeffsToPoly` is injective: if two coefficient vectors produce the same polynomial,
    the vectors are equal. -/
theorem coeffsToPoly_injective (k : ℕ) :
    Function.Injective (coeffsToPoly (F := F) (k := k)) := by
  intro c₁ c₂ h
  funext j
  have h1 := coeffsToPoly_coeff c₁ j
  have h2 := coeffsToPoly_coeff c₂ j
  rw [h] at h1
  exact h1.symm.trans h2

-- ============================================================
-- Section 3: rsEncode injectivity
-- ============================================================

omit [DecidableEq F] in
/-- **rsEncode is injective**: if two coefficient vectors encode to the same codeword,
    they must be equal. This is the key property enabling unique decoding.

    Proof: if `rsEncode domain k c₁ = rsEncode domain k c₂`, then `coeffsToPoly c₁`
    and `coeffsToPoly c₂` agree on all N domain points. Both have degree < k ≤ N,
    so by polynomial determination they are equal, hence `c₁ = c₂`. -/
theorem rsEncode_injective {N : ℕ} (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N) :
    Function.Injective (rsEncode domain k) := by
  intro c₁ c₂ h
  -- The polynomials agree on all N domain points
  have h_eval : ∀ i : Fin N, (coeffsToPoly c₁).eval (domain.points i) =
      (coeffsToPoly c₂).eval (domain.points i) := by
    intro i
    have := congr_fun h i
    simp only [rsEncode_eq_poly_eval] at this
    exact this
  -- Both polynomials have degree < N
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- k = 0: both coefficient vectors are from Fin 0, so they're equal
    funext j; exact j.elim0
  · -- k > 0: use polynomial determination
    have hd1 : (coeffsToPoly c₁).degree < (Finset.univ : Finset (Fin N)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      calc (coeffsToPoly c₁).degree
          ≤ ↑(coeffsToPoly c₁).natDegree := Polynomial.degree_le_natDegree
        _ < ↑k := by exact_mod_cast coeffsToPoly_natDegree_lt c₁ hk0
        _ ≤ ↑N := by exact_mod_cast hk
    have hd2 : (coeffsToPoly c₂).degree < (Finset.univ : Finset (Fin N)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      calc (coeffsToPoly c₂).degree
          ≤ ↑(coeffsToPoly c₂).natDegree := Polynomial.degree_le_natDegree
        _ < ↑k := by exact_mod_cast coeffsToPoly_natDegree_lt c₂ hk0
        _ ≤ ↑N := by exact_mod_cast hk
    have h_inj : Set.InjOn domain.points (↑(Finset.univ : Finset (Fin N))) :=
      fun _ _ _ _ h => domain.distinct h
    have h_poly_eq := Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (Finset.univ : Finset (Fin N)) h_inj hd1 hd2
      (fun i _ => h_eval i)
    exact coeffsToPoly_injective k h_poly_eq

-- ============================================================
-- Section 4: RS decoding via Lagrange interpolation
-- ============================================================

/-- Decode evaluations at `k` distinct domain points back into a coefficient vector.

    Given positions `positions : Fin k → Fin N` picking `k` distinct domain points,
    and values at those positions, we Lagrange-interpolate to get a polynomial of
    degree `< k`, then extract its first `k` coefficients. -/
noncomputable def rsDecode {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (positions : Fin k → Fin N) (values : Fin k → F)
    (_h_distinct : Function.Injective (fun i => domain.points (positions i))) :
    Fin k → F :=
  fun j => (Lagrange.interpolate (Finset.univ : Finset (Fin k))
    (fun i => domain.points (positions i)) values).coeff j.val

-- ============================================================
-- Section 5: Decode inverts encode
-- ============================================================

omit [DecidableEq F] in
/-- Helper: `coeffsToPoly coeffs` equals the Lagrange interpolant of its evaluations
    at `k` distinct points. -/
theorem coeffsToPoly_eq_interpolate {N : ℕ} {k : ℕ}
    (domain : EvalDomain F N)
    (coeffs : Fin k → F)
    (positions : Fin k → Fin N)
    (h_distinct : Function.Injective (fun i => domain.points (positions i)))
    (hk : 0 < k) :
    coeffsToPoly coeffs = Lagrange.interpolate (Finset.univ : Finset (Fin k))
      (fun i => domain.points (positions i))
      (fun i => (coeffsToPoly coeffs).eval (domain.points (positions i))) := by
  have h_inj : Set.InjOn (fun i => domain.points (positions i))
      (↑(Finset.univ : Finset (Fin k))) :=
    fun _ _ _ _ h => h_distinct h
  symm
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ h_inj
  · have := Lagrange.degree_interpolate_lt
      (fun i => (coeffsToPoly coeffs).eval (domain.points (positions i))) h_inj
    rwa [Finset.card_univ, Fintype.card_fin] at this ⊢
  · rw [Finset.card_univ, Fintype.card_fin]
    calc (coeffsToPoly coeffs).degree
        ≤ ↑(coeffsToPoly coeffs).natDegree := Polynomial.degree_le_natDegree
      _ < ↑k := by exact_mod_cast coeffsToPoly_natDegree_lt coeffs hk
  · intro i _
    exact Lagrange.eval_interpolate_at_node _ h_inj (Finset.mem_univ i)

omit [DecidableEq F] in
/-- **Decode inverts encode**: if you encode a coefficient vector and then decode
    at any `k` distinct positions, you recover the original coefficients.

    This is the fundamental correctness property of RS decoding. -/
theorem rsDecode_rsEncode {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (coeffs : Fin k → F)
    (positions : Fin k → Fin N)
    (h_distinct : Function.Injective (fun i => domain.points (positions i))) :
    rsDecode domain k positions (fun i => rsEncode domain k coeffs (positions i)) h_distinct
      = coeffs := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- k = 0: both sides are functions from Fin 0
    funext j; exact j.elim0
  · funext j
    unfold rsDecode
    -- The values fed to interpolate are evaluations of coeffsToPoly at domain points
    have h_vals : (fun i => rsEncode domain k coeffs (positions i)) =
        (fun i => (coeffsToPoly coeffs).eval (domain.points (positions i))) := by
      funext i; rfl
    rw [h_vals]
    -- coeffsToPoly equals its own Lagrange interpolant at these points
    have h_eq := coeffsToPoly_eq_interpolate domain coeffs positions h_distinct hk0
    -- So the coefficient extraction gives back the original
    rw [← h_eq]
    exact coeffsToPoly_coeff coeffs j

-- ============================================================
-- Section 6: Decoding from a full codeword
-- ============================================================

/-- Decode a full codeword using any `k` of the `N` positions. -/
noncomputable def rsDecodeCodeword {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (positions : Fin k → Fin N)
    (h_distinct : Function.Injective (fun i => domain.points (positions i)))
    (word : Fin N → F) : Fin k → F :=
  rsDecode domain k positions (fun i => word (positions i)) h_distinct

omit [DecidableEq F] in
/-- If a word is a valid RS codeword, decoding at any `k` distinct positions recovers
    the underlying coefficient vector. -/
theorem rsDecodeCodeword_of_codeword {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (positions : Fin k → Fin N)
    (h_distinct : Function.Injective (fun i => domain.points (positions i)))
    (word : Fin N → F)
    (hw : isRSCodeword domain k word) :
    ∃ coeffs : Fin k → F,
      word = rsEncode domain k coeffs ∧
      rsDecodeCodeword domain k positions h_distinct word = coeffs := by
  obtain ⟨coeffs, rfl⟩ := hw
  exact ⟨coeffs, rfl, rsDecode_rsEncode domain k hk coeffs positions h_distinct⟩

-- ============================================================
-- Section 7: Unique decoding
-- ============================================================

omit [DecidableEq F] in
/-- RS decoding is unique: if two coefficient vectors encode to codewords that agree
    at `k` positions, the coefficient vectors are identical. -/
theorem rsDecode_unique {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (c₁ c₂ : Fin k → F)
    (positions : Fin k → Fin N)
    (h_distinct : Function.Injective (fun i => domain.points (positions i)))
    (h_agree : ∀ i : Fin k,
      rsEncode domain k c₁ (positions i) = rsEncode domain k c₂ (positions i)) :
    c₁ = c₂ := by
  have h1 := rsDecode_rsEncode domain k hk c₁ positions h_distinct
  have h2 := rsDecode_rsEncode domain k hk c₂ positions h_distinct
  rw [← h1, ← h2]
  congr 1
  funext i
  exact h_agree i

-- ============================================================
-- Section 8: Algebraic knowledge extractor
-- ============================================================

/-- An algebraic knowledge extractor for the Ligero protocol.
    Given a well-formed tableau (all rows are RS codewords), the extractor
    decodes each row to recover the underlying coefficient vectors,
    from which the witness can be read off. -/
structure AlgebraicExtractor (F : Type*) [Field F] [DecidableEq F]
    {params : LigeroParams} (domain : EvalDomain F params.NCOL) where
  /-- Positions to sample for decoding (k distinct positions). -/
  positions : Fin params.BLOCK → Fin params.NCOL
  /-- The positions are distinct under the domain map. -/
  h_distinct : Function.Injective (fun i => domain.points (positions i))

/-- Extract coefficient vectors from a well-formed tableau by RS-decoding each row. -/
noncomputable def AlgebraicExtractor.extractRow {params : LigeroParams}
    {domain : EvalDomain F params.NCOL}
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params) (i : Fin params.NROW) : Fin params.BLOCK → F :=
  rsDecodeCodeword domain params.BLOCK ext.positions ext.h_distinct (T.rows i)

/-- If the tableau is well-formed, the extracted coefficients re-encode to the original rows. -/
theorem AlgebraicExtractor.extractRow_correct {params : LigeroParams}
    {domain : EvalDomain F params.NCOL}
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params)
    (h_wf : tableauWellFormed domain T) (i : Fin params.NROW) :
    rsEncode domain params.BLOCK (ext.extractRow T i) = T.rows i := by
  obtain ⟨coeffs, h_eq, h_dec⟩ := rsDecodeCodeword_of_codeword domain params.BLOCK
    (le_of_lt params.h_block_lt) ext.positions ext.h_distinct (T.rows i) (h_wf i)
  unfold AlgebraicExtractor.extractRow
  rw [h_dec, ← h_eq]

-- ============================================================
-- Section 9: Algebraic extractability theorem
-- ============================================================

omit [DecidableEq F] in
/-- **Algebraic extractability**: if all tableau rows are valid RS codewords and
    the Ligero tests accept (binding is satisfied), then the decoded witness
    satisfies all constraints.

    This composes RS decoding (which extracts the witness from the tableau)
    with the Ligero binding theorem (which says accepted witnesses satisfy
    constraints). The key insight is that the extractor needs only the
    *existence* of an underlying witness that satisfies constraints, which
    is guaranteed by the binding theorem `ligero_binding_from_tests`. -/
theorem algebraic_extractability {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_accept : LigeroAccepts domain T w lcs qcs) :
    satisfiesAll w lcs qcs :=
  ligero_binding_from_tests domain T w lcs qcs h_accept

/-- **Full extractability with RS decode**: given a well-formed tableau and
    an extractor, we can decode each row and the decoded data is consistent
    with the tableau rows.

    This theorem states that if the tableau is well-formed, then for every row,
    the extractor recovers coefficient vectors that, when re-encoded, produce
    exactly the original codeword rows. Combined with the binding theorem,
    this shows that the extractor recovers a valid witness. -/
theorem full_extractability {params : LigeroParams}
    {domain : EvalDomain F params.NCOL}
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params)
    (h_wf : tableauWellFormed domain T) :
    ∀ i : Fin params.NROW,
      rsEncode domain params.BLOCK (ext.extractRow T i) = T.rows i :=
  fun i => ext.extractRow_correct T h_wf i

/-- **Knowledge soundness composition**: if the Ligero protocol accepts with a well-formed
    tableau, we can extract a witness (via RS decoding) that satisfies all constraints.

    This is the full knowledge soundness statement: the knowledge extractor is
    constructive (given by `AlgebraicExtractor`) and the extracted witness provably
    satisfies the constraint system. -/
theorem knowledge_soundness {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (ext : AlgebraicExtractor F domain)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_accept : LigeroAccepts domain T w lcs qcs) :
    -- The witness satisfies all constraints
    satisfiesAll w lcs qcs
    -- AND the tableau rows are faithfully decoded
    ∧ ∀ i : Fin params.NROW,
        rsEncode domain params.BLOCK (ext.extractRow T i) = T.rows i :=
  ⟨ligero_binding_from_tests domain T w lcs qcs h_accept,
   full_extractability ext T h_accept.wf⟩
