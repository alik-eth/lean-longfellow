import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-! # Padded Sumcheck

This file defines a masking / padding mechanism for the sumcheck protocol.
Each round's prover polynomial is shifted by a "mask" polynomial, so the
verifier sees `g_i - m_i` instead of `g_i`.  When the masks telescope
consistently, the padded verifier accepts iff the unpadded verifier would
accept with the claimed sum shifted by a single scalar `pad_offset`.
-/

/-- A sumcheck pad: one masking polynomial per round. -/
structure SumcheckPad (F : Type*) [Field F] (n : ℕ) where
  masks : Fin n → Polynomial F

/-- Apply padding: subtract the mask from each round's polynomial.
    Challenges are unchanged. -/
noncomputable def paddedRounds (rounds : Fin n → SumcheckRound F) (pad : SumcheckPad F n) :
    Fin n → SumcheckRound F :=
  fun i => ⟨(rounds i).prover_poly - pad.masks i, (rounds i).challenge⟩

-- ---------------------------------------------------------------------------
-- Basic lemmas
-- ---------------------------------------------------------------------------

/-- The padded polynomial evaluates as the original minus the mask. -/
theorem paddedRounds_eval (rounds : Fin n → SumcheckRound F) (pad : SumcheckPad F n)
    (i : Fin n) (x : F) :
    (paddedRounds rounds pad i).prover_poly.eval x =
      (rounds i).prover_poly.eval x - (pad.masks i).eval x := by
  simp [paddedRounds, Polynomial.eval_sub]

/-- Padding does not change the verifier's challenge. -/
theorem paddedRounds_challenge (rounds : Fin n → SumcheckRound F) (pad : SumcheckPad F n)
    (i : Fin n) :
    (paddedRounds rounds pad i).challenge = (rounds i).challenge := by
  simp [paddedRounds]

-- ---------------------------------------------------------------------------
-- Consistency predicate
-- ---------------------------------------------------------------------------

/-- A pad is *consistent* if the mask sums telescope like the verifier checks.

For round 0 the mask sum equals `pad_offset`; for round `i > 0` it equals the
previous mask evaluated at the previous challenge. -/
def padConsistent (pad : SumcheckPad F n) (pad_offset : F)
    (challenges : Fin n → F) : Prop :=
  ∀ i : Fin n,
    (pad.masks i).eval 0 + (pad.masks i).eval 1 =
      if (i : ℕ) = 0 then pad_offset
      else (pad.masks ⟨i.val - 1, by omega⟩).eval (challenges ⟨i.val - 1, by omega⟩)

-- ---------------------------------------------------------------------------
-- Main theorem
-- ---------------------------------------------------------------------------

/-- With consistent padding, the sum-check conditions on padded rounds are
    equivalent to those on unpadded rounds with `claimed_sum` shifted by
    `pad_offset`. -/
theorem padded_sum_check_iff
    {claimed_sum pad_offset : F}
    {rounds : Fin n → SumcheckRound F}
    {pad : SumcheckPad F n}
    (hpad : padConsistent pad pad_offset (fun i => (rounds i).challenge)) :
    (∀ i : Fin n,
      (paddedRounds rounds pad i).prover_poly.eval 0 +
      (paddedRounds rounds pad i).prover_poly.eval 1 =
        if (i : ℕ) = 0 then (claimed_sum - pad_offset)
        else (paddedRounds rounds pad ⟨i.val - 1, by omega⟩).prover_poly.eval
              (rounds ⟨i.val - 1, by omega⟩).challenge) ↔
    (∀ i : Fin n,
      (rounds i).prover_poly.eval 0 + (rounds i).prover_poly.eval 1 =
        if (i : ℕ) = 0 then claimed_sum
        else (rounds ⟨i.val - 1, by omega⟩).prover_poly.eval
              (rounds ⟨i.val - 1, by omega⟩).challenge) := by
  -- Shorthands
  let g := fun i => (rounds i).prover_poly
  let m := pad.masks
  let r := fun i => (rounds i).challenge
  constructor
  · -- padded → unpadded
    intro hP i
    by_cases h0 : (i : ℕ) = 0
    · -- round 0
      simp only [h0, ↓reduceIte]
      have hPi : (g i).eval 0 - (m i).eval 0 + ((g i).eval 1 - (m i).eval 1) = claimed_sum - pad_offset := by
        have := hP i
        simp only [paddedRounds_eval, h0, ↓reduceIte] at this
        exact this
      have hm_i : (m i).eval 0 + (m i).eval 1 = pad_offset := by
        have := hpad i; simp only [h0, ↓reduceIte] at this; exact this
      linear_combination hPi + hm_i
    · -- round i > 0
      simp only [h0, ↓reduceIte]
      have hPi : (g i).eval 0 - (m i).eval 0 + ((g i).eval 1 - (m i).eval 1) =
                 (g ⟨i.val - 1, by omega⟩).eval (r ⟨i.val - 1, by omega⟩) -
                 (m ⟨i.val - 1, by omega⟩).eval (r ⟨i.val - 1, by omega⟩) := by
        have := hP i
        simp only [paddedRounds_eval, h0, ↓reduceIte] at this
        exact this
      have hm_i : (m i).eval 0 + (m i).eval 1 = (m ⟨i.val - 1, by omega⟩).eval (r ⟨i.val - 1, by omega⟩) := by
        have := hpad i; simp only [h0, ↓reduceIte] at this; exact this
      linear_combination hPi + hm_i
  · -- unpadded → padded
    intro hU i
    by_cases h0 : (i : ℕ) = 0
    · simp only [paddedRounds_eval, h0, ↓reduceIte]
      have hUi : (g i).eval 0 + (g i).eval 1 = claimed_sum := by
        have := hU i; simp only [h0, ↓reduceIte] at this; exact this
      have hm_i : (m i).eval 0 + (m i).eval 1 = pad_offset := by
        have := hpad i; simp only [h0, ↓reduceIte] at this; exact this
      linear_combination hUi - hm_i
    · simp only [paddedRounds_eval, h0, ↓reduceIte]
      have hUi : (g i).eval 0 + (g i).eval 1 =
                 (g ⟨i.val - 1, by omega⟩).eval (r ⟨i.val - 1, by omega⟩) := by
        have := hU i; simp only [h0, ↓reduceIte] at this; exact this
      have hm_i : (m i).eval 0 + (m i).eval 1 = (m ⟨i.val - 1, by omega⟩).eval (r ⟨i.val - 1, by omega⟩) := by
        have := hpad i; simp only [h0, ↓reduceIte] at this; exact this
      linear_combination hUi - hm_i

-- ---------------------------------------------------------------------------
-- Final evaluation check
-- ---------------------------------------------------------------------------

/-- Padding preserves the final evaluation check up to the last mask value.

The padded prover's last polynomial, evaluated at the last challenge, equals
the multilinear extension value minus the last mask value.  The biconditional
is therefore trivially equivalent to the unpadded check once we know the mask
contribution. -/
theorem padded_final_check
    {p : MultilinearPoly F n}
    {rounds : Fin n → SumcheckRound F}
    {pad : SumcheckPad F n}
    (hn : 0 < n) :
    let last : Fin n := ⟨n - 1, by omega⟩
    (paddedRounds rounds pad last).prover_poly.eval (rounds last).challenge =
      p.eval (fun i => (rounds i).challenge) - (pad.masks last).eval (rounds last).challenge ↔
    (rounds last).prover_poly.eval (rounds last).challenge =
      p.eval (fun i => (rounds i).challenge) := by
  simp only [paddedRounds_eval]
  -- goal: g(r) - m(r) = eval p - m(r) ↔ g(r) = eval p
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h
