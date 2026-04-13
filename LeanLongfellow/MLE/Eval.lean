import LeanLongfellow.MLE.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fin.Tuple.Basic

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

/-- Fix the first variable to `a`, yielding an `n`-variate MLE.
    Table entry: `(1 - a) · p.table(false :: b) + a · p.table(true :: b)`. -/
def partialEvalFirst (p : MultilinearPoly F (n + 1)) (a : F) : MultilinearPoly F n where
  table b := (1 - a) * p.table (Fin.cons false b) + a * p.table (Fin.cons true b)

/-- Sum over all but the first variable, producing a univariate polynomial.
    This is the honest prover's message in each sumcheck round.
    `sumFirstVar p = C(c₀) + X · C(c₁ - c₀)` where
    `c₀ = ∑_b p.table(0::b)`, `c₁ = ∑_b p.table(1::b)`. -/
noncomputable def sumFirstVar (p : MultilinearPoly F (n + 1)) : Polynomial F :=
  let c0 := ∑ b : Fin n → Bool, p.table (Fin.cons false b)
  let c1 := ∑ b : Fin n → Bool, p.table (Fin.cons true b)
  Polynomial.C c0 + Polynomial.X * Polynomial.C (c1 - c0)

theorem sumFirstVar_eval_zero (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 0 = ∑ b : Fin n → Bool, p.table (Fin.cons false b) := by
  simp [sumFirstVar, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_finset_sum, Polynomial.eval_C]

theorem sumFirstVar_eval_one (p : MultilinearPoly F (n + 1)) :
    (sumFirstVar p).eval 1 = ∑ b : Fin n → Bool, p.table (Fin.cons true b) := by
  simp [sumFirstVar, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_finset_sum, Polynomial.eval_C]

theorem lagrangeBasis_cons (b₀ : Bool) (b : Fin n → Bool) (a : F) (x : Fin n → F) :
    lagrangeBasis (Fin.cons b₀ b) (Fin.cons a x) =
      (if b₀ then a else 1 - a) * lagrangeBasis b x := by
  simp only [lagrangeBasis]
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

theorem partialEval_table_sum (p : MultilinearPoly F (n + 1)) (r : F) :
    (∑ b : Fin n → Bool, (partialEvalFirst p r).table b) = (sumFirstVar p).eval r := by
  simp only [partialEvalFirst, sumFirstVar, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  ring

theorem partialEvalFirst_eval (p : MultilinearPoly F (n + 1)) (r : F) (x : Fin n → F) :
    (partialEvalFirst p r).eval x = p.eval (Fin.cons r x) := by
  simp only [eval, partialEvalFirst]
  -- Decompose RHS sum over Fin (n+1) → Bool into sum over Bool × (Fin n → Bool)
  have hrhs : ∑ b' : Fin (n + 1) → Bool, p.table b' * lagrangeBasis b' (Fin.cons r x) =
      ∑ b₀ : Bool, ∑ b : Fin n → Bool,
        p.table (Fin.cons b₀ b) * lagrangeBasis (Fin.cons b₀ b) (Fin.cons r x) := by
    trans ∑ p_1 : Bool × (Fin n → Bool),
        p.table (Fin.cons p_1.1 p_1.2) * lagrangeBasis (Fin.cons p_1.1 p_1.2) (Fin.cons r x)
    · apply Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)).symm
      intro p_1
      simp [Fin.consEquiv]
    · exact Fintype.sum_prod_type _
  rw [hrhs]
  simp only [lagrangeBasis_cons]
  simp only [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros; ring

end MultilinearPoly
