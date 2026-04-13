import LeanLongfellow.MLE.Eval

open Finset

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Two multilinear polynomials with the same evaluation table are equal. -/
theorem mle_unique (p q : MultilinearPoly F n) (h : p.table = q.table) :
    ∀ x : Fin n → F, p.eval x = q.eval x := by
  intro x
  simp only [eval, h]

/-- Any function on `{0,1}^n` has a unique multilinear extension.
    Specifically, for any `f : (Fin n → Bool) → F`, the polynomial `⟨f⟩`
    is the unique MLE that agrees with `f` on the Boolean hypercube. -/
theorem mle_extension_exists (f : (Fin n → Bool) → F) :
    ∃! p : MultilinearPoly F n, ∀ b, p.eval (boolToField b) = f b := by
  refine ⟨⟨f⟩, ?_, ?_⟩
  · -- Existence: show ⟨f⟩.eval (boolToField b) = f b for all b
    intro b
    rw [eval_boolVec]
  · -- Uniqueness: if p.eval (boolToField b) = f b for all b, then p = ⟨f⟩
    intro p hp
    have htable : p.table = f := by
      funext b
      rw [← eval_boolVec p b]
      exact hp b
    cases p
    congr

end MultilinearPoly
