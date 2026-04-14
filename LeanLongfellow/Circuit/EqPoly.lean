import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval

open Finset MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-! # EQ Polynomial

The multilinear extension of the equality indicator function.
`eqPoly(t, x) = ∏ᵢ (tᵢ·xᵢ + (1-tᵢ)·(1-xᵢ))`.

On the Boolean hypercube, this is the Kronecker delta:
`eqPoly(t, b) = 1` if `t = b`, `0` otherwise.
-/

/-- The EQ polynomial: multilinear extension of the equality indicator.
    `eq(t, x) = ∏ᵢ (tᵢ·xᵢ + (1-tᵢ)·(1-xᵢ))` -/
noncomputable def eqPoly (t : Fin n → F) (x : Fin n → F) : F :=
  ∏ i : Fin n, (t i * x i + (1 - t i) * (1 - x i))

/-- eqPoly at a Boolean first argument equals lagrangeBasis. -/
theorem eqPoly_eq_lagrangeBasis (b : Fin n → Bool) (x : Fin n → F) :
    eqPoly (boolToField b) x = lagrangeBasis b x := by
  simp only [eqPoly, lagrangeBasis]
  apply Finset.prod_congr rfl
  intro i _
  simp only [boolToField]
  cases b i <;> simp

/-- On the Boolean hypercube, eqPoly is the Kronecker delta. -/
theorem eqPoly_bool (t b : Fin n → Bool) :
    eqPoly (boolToField t) (boolToField b) = if t = b then (1 : F) else 0 := by
  rw [eqPoly_eq_lagrangeBasis]
  exact lagrangeBasis_indicator t b

/-- eqPoly selects a single term from a sum over the hypercube. -/
theorem eqPoly_select (t : Fin n → Bool) (f : (Fin n → Bool) → F) :
    ∑ b : Fin n → Bool, eqPoly (boolToField t) (boolToField b) * f b = f t := by
  simp only [eqPoly_bool]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_univ]

/-- Summing eqPoly over the Boolean hypercube gives 1. -/
theorem eqPoly_sum (t : Fin n → Bool) :
    ∑ b : Fin n → Bool, eqPoly (F := F) (boolToField t) (boolToField b) = 1 := by
  have := eqPoly_select t (fun _ => (1 : F))
  simpa using this

/-- eqPoly with a general first argument and Boolean second argument equals lagrangeBasis.
    `eqPoly t (boolToField g) = lagrangeBasis g t` -/
theorem eqPoly_comm_boolToField (t : Fin n → F) (g : Fin n → Bool) :
    eqPoly t (boolToField g) = lagrangeBasis g t := by
  simp only [eqPoly, lagrangeBasis, boolToField]
  apply Finset.prod_congr rfl
  intro i _
  cases g i <;> simp [mul_comm]

/-- Summing `eqPoly(t, boolToField g) * f(g)` over the Boolean hypercube
    computes the MLE evaluation. Works for any `t ∈ F^n`. -/
theorem eqPoly_eval (t : Fin n → F) (p : MultilinearPoly F n) :
    ∑ g : Fin n → Bool, eqPoly t (boolToField g) * p.table g = p.eval t := by
  simp only [eqPoly_comm_boolToField, eval]
  apply Finset.sum_congr rfl
  intro g _
  ring
