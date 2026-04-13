import LeanLongfellow.MLE.Eval
import Mathlib.Algebra.Polynomial.Degree.Defs

open Finset Polynomial

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- The sum of a multilinear polynomial over the Boolean hypercube
    equals the sum of its evaluation table. -/
theorem mle_sum_hypercube (p : MultilinearPoly F n) :
    ∑ b : Fin n → Bool, p.eval (boolToField b) = ∑ b : Fin n → Bool, p.table b := by
  apply Finset.sum_congr rfl
  intro b _
  exact eval_boolVec p b

/-- The honest prover polynomial has degree ≤ 1. -/
theorem sumFirstVar_natDegree_le (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).natDegree ≤ 1 := by
  unfold sumFirstVar
  apply le_trans (natDegree_add_le _ _)
  apply max_le
  · rw [natDegree_C]; exact Nat.zero_le _
  · calc (X * C _).natDegree
        ≤ X.natDegree + (C _).natDegree := natDegree_mul_le
      _ ≤ 1 + 0 := by rw [natDegree_C]; exact Nat.add_le_add_right natDegree_X_le 0
      _ = 1 := by omega

/-- The sum of `sumFirstVar(p)` at 0 and 1 equals the full table sum. -/
theorem sumFirstVar_sum (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 0 + (sumFirstVar p).eval 1 =
      ∑ b : Fin (n + 1) → Bool, p.table b := by
  rw [sumFirstVar_eval_zero, sumFirstVar_eval_one]
  have : ∑ b' : Fin (n + 1) → Bool, p.table b' =
      ∑ b₀ : Bool, ∑ b : Fin n → Bool, p.table (Fin.cons b₀ b) := by
    trans ∑ p_1 : Bool × (Fin n → Bool), p.table (Fin.cons p_1.1 p_1.2)
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)).symm
      intro p_1
      simp [Fin.consEquiv]
    · exact Fintype.sum_prod_type _
  rw [this, Fintype.sum_bool]
  ring

end MultilinearPoly
