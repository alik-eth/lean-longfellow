import LeanLongfellow.MLE.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open Finset

namespace MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-- Evaluate the multilinear extension at any point `x ∈ F^n`. -/
def eval (p : MultilinearPoly F n) (x : Fin n → F) : F :=
  ∑ b : Fin n → Bool, p.table b * lagrangeBasis b x

theorem lagrangeBasis_indicator (b b' : Fin n → Bool) :
    lagrangeBasis (F := F) b (boolToField b') = if b = b' then 1 else 0 := by
  simp only [lagrangeBasis, boolToField]
  split
  case isTrue h =>
    subst h
    apply Finset.prod_eq_one
    intro i _
    split <;> simp
  case isFalse h =>
    have ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    revert hi
    cases b i <;> cases b' i <;> simp

theorem eval_boolVec (p : MultilinearPoly F n) (b : Fin n → Bool) :
    p.eval (boolToField b) = p.table b := by
  simp only [eval]
  conv_lhs =>
    arg 2
    ext b'
    rw [lagrangeBasis_indicator]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]

end MultilinearPoly
