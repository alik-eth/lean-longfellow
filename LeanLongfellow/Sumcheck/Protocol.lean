import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Props
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Polynomial MultilinearPoly

/-! # Sumcheck Protocol Model

This file defines the sumcheck protocol model: the round structure,
the verifier's accept predicate, and the honest prover.
-/

/-- A single round of the sumcheck protocol. -/
structure SumcheckRound (F : Type*) [Field F] where
  /-- Prover sends a univariate polynomial -/
  prover_poly : Polynomial F
  /-- Verifier sends a random challenge -/
  challenge : F

/-- The verifier's accept predicate for the sumcheck protocol. -/
def verifierAccepts {F : Type*} [Field F] {n : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F) : Prop :=
  -- Sum check: each round polynomial sums correctly
  (∀ i : Fin n,
    (rounds i).prover_poly.eval 0 + (rounds i).prover_poly.eval 1 =
      if (i : ℕ) = 0 then claimed_sum
      else (rounds ⟨i.val - 1, by omega⟩).prover_poly.eval
            (rounds ⟨i.val - 1, by omega⟩).challenge) ∧
  -- Final evaluation check
  (∀ (hn : 0 < n),
    let last : Fin n := ⟨n - 1, by omega⟩
    (rounds last).prover_poly.eval (rounds last).challenge =
      p.eval (fun i => (rounds i).challenge))

/-- The honest prover, defined recursively.
    `m + (k+1) = (m+k) + 1` is definitional in Lean 4, so `partialEvalFirst` applies
    without casts. `Fin.cases` splits `Fin (n+1)` into 0 and `Fin.succ j`. -/
noncomputable def honestProver {F : Type*} [Field F] {n : ℕ} :
    MultilinearPoly F n → (Fin n → F) → Fin n → SumcheckRound F :=
  match n with
  | 0 => fun _ _ => Fin.elim0
  | _ + 1 => fun p challenges => Fin.cases
      ⟨p.sumFirstVar, challenges 0⟩
      (fun j => honestProver (p.partialEvalFirst (challenges 0)) (fun k => challenges k.succ) j)

@[simp] theorem honestProver_zero {F : Type*} [Field F] {m : ℕ}
    (p : MultilinearPoly F (m + 1)) (challenges : Fin (m + 1) → F) :
    honestProver p challenges 0 = ⟨p.sumFirstVar, challenges 0⟩ := by
  simp [honestProver, Fin.cases]

@[simp] theorem honestProver_succ {F : Type*} [Field F] {m : ℕ}
    (p : MultilinearPoly F (m + 1)) (challenges : Fin (m + 1) → F) (j : Fin m) :
    honestProver p challenges j.succ =
      honestProver (p.partialEvalFirst (challenges 0))
        (fun k => challenges k.succ) j := by
  simp [honestProver, Fin.cases]
