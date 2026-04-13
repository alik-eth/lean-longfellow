import LeanLongfellow.MLE.Defs
import LeanLongfellow.MLE.Eval
import LeanLongfellow.MLE.Props
import Mathlib.Algebra.Polynomial.Eval.Defs

open Finset Polynomial MultilinearPoly

/-! # Sumcheck Protocol Model

This file defines the sumcheck protocol model: the round structure,
the verifier's accept predicate, iterated partial evaluation, and
the honest prover.
-/

/-- A single round of the sumcheck protocol. -/
structure SumcheckRound (F : Type*) [Field F] where
  /-- Prover sends a univariate polynomial -/
  prover_poly : Polynomial F
  /-- Verifier sends a random challenge -/
  challenge : F

variable {F : Type*} [Field F] {n : ℕ}

/-- The verifier's accept predicate for the sumcheck protocol. -/
def verifierAccepts (p : MultilinearPoly F n) (claimed_sum : F)
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

/-- Apply `partialEvalFirst` `k` times. -/
noncomputable def iterPartialEval (F : Type*) [Field F] :
    (m : ℕ) → MultilinearPoly F m → (k : ℕ) → (hk : k ≤ m) →
    (Fin k → F) → MultilinearPoly F (m - k)
  | m, p, 0, _, _ => by rwa [Nat.sub_zero]
  | m + 1, p, k + 1, hk, challenges => by
    have : m + 1 - (k + 1) = m - k := by omega
    rw [this]
    exact iterPartialEval F m (p.partialEvalFirst (challenges ⟨0, by omega⟩))
      k (by omega) (fun i => challenges ⟨i.val + 1, by omega⟩)

/-- The honest prover for the sumcheck protocol.
    At round i, after fixing variables 0..i-1, compute `sumFirstVar` of
    the remaining polynomial. -/
noncomputable def honestProver (p : MultilinearPoly F n) (challenges : Fin n → F) :
    Fin n → SumcheckRound F :=
  fun i => {
    prover_poly := by
      have h : n - i.val = (n - i.val - 1) + 1 := by omega
      exact (h ▸ iterPartialEval F n p i.val (le_of_lt i.isLt)
        (fun j => challenges ⟨j.val, by omega⟩)).sumFirstVar
    challenge := challenges i
  }
