import LeanLongfellow.Ligero.ReedSolomon.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Degree bound for `coeffsToPoly` -/

omit [DecidableEq F] in
/-- The polynomial `coeffsToPoly coeffs` has `natDegree ≤ k - 1` (equivalently `< k` when `k > 0`).
    This follows because it is a sum of `C(aⱼ) * X^j` for `j < k`. -/
theorem coeffsToPoly_natDegree_le {k : ℕ} (coeffs : Fin k → F) :
    (coeffsToPoly coeffs).natDegree ≤ k - 1 := by
  unfold coeffsToPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt i.isLt)

omit [DecidableEq F] in
theorem coeffsToPoly_natDegree_lt {k : ℕ} (coeffs : Fin k → F) (hk : 0 < k) :
    (coeffsToPoly coeffs).natDegree < k :=
  Nat.lt_of_le_of_lt (coeffsToPoly_natDegree_le coeffs) (Nat.sub_lt hk Nat.le.refl)

/-! ### Reed-Solomon distance / agreement bound -/

/-- Two distinct RS codewords of degree < k over an N-point domain agree on at most k - 1
    positions. This is the key distance property of Reed-Solomon codes. -/
theorem rs_agreement_bound {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (_hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂) :
    (Finset.univ.filter (fun i => w₁ i = w₂ i)).card ≤ k - 1 := by
  -- Extract the underlying polynomials
  obtain ⟨c₁, rfl⟩ := hw₁
  obtain ⟨c₂, rfl⟩ := hw₂
  -- Let d = p₁ - p₂ be the difference polynomial
  set p₁ := coeffsToPoly c₁
  set p₂ := coeffsToPoly c₂
  set d := p₁ - p₂ with hd_def
  -- d is nonzero because w₁ ≠ w₂
  have hd_ne : d ≠ 0 := by
    intro hd0
    apply hne
    funext i
    simp only [rsEncode_eq_poly_eval]
    have : d.eval (domain.points i) = 0 := by rw [hd0]; simp
    rwa [Polynomial.eval_sub, sub_eq_zero] at this
  -- The agreement set maps into roots of d via domain.points
  -- We show: card(agree) ≤ card(d.roots.toFinset) ≤ card(d.roots) ≤ d.natDegree ≤ k - 1
  -- Step 1: The image of the agreement set under domain.points is a subset of d.roots.toFinset
  have agree_subset : (univ.filter (fun i => rsEncode domain k c₁ i = rsEncode domain k c₂ i)).image
      domain.points ⊆ d.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hd_ne]
    simp only [rsEncode_eq_poly_eval] at hi
    rw [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero]
    exact hi.2
  -- Step 2: domain.points is injective on the agreement set
  have inj : Set.InjOn domain.points (univ.filter (fun i =>
      rsEncode domain k c₁ i = rsEncode domain k c₂ i) : Set (Fin N)) :=
    fun _ _ _ _ h => domain.distinct h
  -- Step 3: card(agree) = card(image) because of injectivity
  have card_eq : (univ.filter (fun i => rsEncode domain k c₁ i = rsEncode domain k c₂ i)).card =
      ((univ.filter (fun i => rsEncode domain k c₁ i = rsEncode domain k c₂ i)).image
        domain.points).card :=
    (Finset.card_image_of_injOn inj).symm
  -- Step 4: chain the inequalities
  rw [card_eq]
  calc ((univ.filter (fun i => rsEncode domain k c₁ i = rsEncode domain k c₂ i)).image
        domain.points).card
      ≤ d.roots.toFinset.card := Finset.card_le_card agree_subset
    _ ≤ Multiset.card d.roots := Multiset.toFinset_card_le _
    _ ≤ d.natDegree := Polynomial.card_roots' d
    _ ≤ k - 1 := by
        calc d.natDegree
            ≤ max p₁.natDegree p₂.natDegree := Polynomial.natDegree_sub_le p₁ p₂
          _ ≤ max (k - 1) (k - 1) := by
              apply max_le_max (coeffsToPoly_natDegree_le c₁) (coeffsToPoly_natDegree_le c₂)
          _ = k - 1 := max_self _
