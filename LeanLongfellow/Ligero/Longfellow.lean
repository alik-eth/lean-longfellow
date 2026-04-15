import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Generate
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F]
variable {q : ℕ}

/-! # End-to-End Longfellow Soundness

This file proves the capstone theorem: if Ligero binding holds and the
verifier accepts a wrong claim, then a challenge must have hit a root
of a nonzero degree-≤-1 polynomial.

The key design fix: we reconstruct sumcheck rounds from an ARBITRARY
satisfying witness (given by Ligero binding), rather than assuming
the witness came from honest encoding.
-/

-- ============================================================
-- Section 1: Decode rounds from witness
-- ============================================================

/-- Reconstruct a degree-≤-1 polynomial from its evaluations at 0 and 1. -/
noncomputable def polyFromEvals (v0 v1 : F) : F[X] :=
  Polynomial.C v0 + Polynomial.C (v1 - v0) * Polynomial.X

omit [DecidableEq F] in
theorem polyFromEvals_eval_zero (v0 v1 : F) :
    (polyFromEvals v0 v1).eval 0 = v0 := by
  simp [polyFromEvals, eval_add, eval_mul, eval_C, eval_X]

omit [DecidableEq F] in
theorem polyFromEvals_eval_one (v0 v1 : F) :
    (polyFromEvals v0 v1).eval 1 = v1 := by
  simp [polyFromEvals, eval_add, eval_mul, eval_C, eval_X]

omit [DecidableEq F] in
theorem polyFromEvals_eval (v0 v1 r : F) :
    (polyFromEvals v0 v1).eval r = (1 - r) * v0 + r * v1 := by
  simp [polyFromEvals, eval_add, eval_mul, eval_C, eval_X]; ring

omit [DecidableEq F] in
theorem polyFromEvals_natDegree (v0 v1 : F) :
    (polyFromEvals v0 v1).natDegree ≤ 1 := by
  unfold polyFromEvals
  calc (Polynomial.C v0 + Polynomial.C (v1 - v0) * Polynomial.X).natDegree
      ≤ max (Polynomial.C v0).natDegree
            (Polynomial.C (v1 - v0) * Polynomial.X).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ max 0 (Polynomial.C (v1 - v0) * Polynomial.X).natDegree := by
        simp [Polynomial.natDegree_C]
    _ ≤ max 0 ((Polynomial.C (v1 - v0)).natDegree + Polynomial.X.natDegree) := by
        gcongr; exact Polynomial.natDegree_mul_le
    _ ≤ max 0 (0 + 1) := by
        simp [Polynomial.natDegree_C, Polynomial.natDegree_X]
    _ = 1 := by norm_num

/-- Reconstruct sumcheck rounds from a witness vector and challenges.
    Round i has polynomial determined by w[2i], w[2i+1] and challenge = challenges i. -/
noncomputable def decodeRounds {n : ℕ} (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F) : Fin n → SumcheckRound F :=
  fun i => {
    prover_poly := polyFromEvals
      (w ⟨2 * i.val, by unfold witnessSize; omega⟩)
      (w ⟨2 * i.val + 1, by unfold witnessSize; omega⟩)
    challenge := challenges i
  }

-- ============================================================
-- Section 2: Bridge theorem for arbitrary witnesses
-- ============================================================

omit [DecidableEq F] in
/-- If an arbitrary witness satisfies the generated constraints, then
    verifierAccepts holds on the decoded rounds.

    This is the correct direction: Ligero binding gives us an arbitrary
    satisfying witness, and we reconstruct rounds from it. -/
theorem witness_satisfies_implies_verifierAccepts {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (w : Fin (witnessSize n) → F)
    (h_sat : satisfiesLinear w (generateConstraints claimed_sum challenges))
    (h_final : satisfiesLinear w (generateFinalConstraint p challenges)) :
    verifierAccepts p claimed_sum (decodeRounds w challenges) := by
  constructor
  · -- Sum check: each round polynomial sums correctly
    intro i
    have hi_sat := h_sat i
    rw [sparse_sum_eq] at hi_sat
    -- Simplify the LHS using polyFromEvals
    simp only [decodeRounds, polyFromEvals_eval_zero, polyFromEvals_eval_one]
    simp only [generateConstraints] at hi_sat
    by_cases hi0 : (i : ℕ) = 0
    · -- i = 0
      simp only [hi0, show ¬(0 > 0) from by omega, ↓reduceIte, add_zero] at hi_sat
      simp only [hi0, ↓reduceIte]; exact hi_sat
    · -- i > 0
      have hig : (i : ℕ) > 0 := Nat.pos_of_ne_zero hi0
      simp only [hig, ↓reduceIte, hi0] at hi_sat
      simp only [hi0, ↓reduceIte]
      -- Goal: w[2i] + w[2i+1] = polyFromEvals(w[2(i-1)], w[2(i-1)+1]).eval (challenges ⟨i-1, _⟩)
      rw [polyFromEvals_eval]
      -- Goal: w[2i] + w[2i+1] = (1 - c) * w[2(i-1)] + c * w[2(i-1)+1]
      -- hi_sat: w[2i] + w[2i+1] + (-(1-c)*w[2(i-1)] + (-c)*w[2(i-1)+1]) = 0
      linear_combination hi_sat
  · -- Final evaluation check
    intro hn
    have hf := h_final ⟨0, by omega⟩
    rw [sparse_final_sum_eq hn] at hf
    simp only [generateFinalConstraint] at hf
    simp only [decodeRounds]
    show (polyFromEvals
      (w ⟨2 * (n - 1), by unfold witnessSize; omega⟩)
      (w ⟨2 * (n - 1) + 1, by unfold witnessSize; omega⟩)).eval
        (challenges ⟨n - 1, by omega⟩) = p.eval (fun i => challenges i)
    rw [polyFromEvals_eval]
    -- Goal: (1-c)*w[2(n-1)] + c*w[2(n-1)+1] = p.eval challenges
    -- hf: (1-c)*w[2(n-1)] + c*w[2(n-1)+1] = p.eval challenges
    have hfun : (fun i : Fin n => challenges i) = challenges := by ext; rfl
    rw [hfun]; exact hf

-- ============================================================
-- Section 3: Longfellow soundness
-- ============================================================

/-- **End-to-end Longfellow soundness (combined):**
    If Ligero binding holds and the verifier accepts with a wrong claim,
    then there exists a round where the challenge hits a root of a
    nonzero degree-≤-1 polynomial.

    This is the main theorem composing:
    1. Ligero binding → witness satisfies constraints
    2. Constraint satisfaction → verifierAccepts on decoded rounds
    3. sumcheck_soundness_det → root hit -/
theorem longfellow_soundness {n : ℕ}
    [L : LigeroScheme F (witnessSize n) (n + 1) q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (ligeroProof : L.Proof)
    -- Ligero accepted with ALL constraints (n sumcheck + 1 final)
    (hligero : L.verify (L.commit w)
      (generateAllConstraints p claimed_sum challenges) qcs ligeroProof) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 := by
  -- Step 1: Ligero binding gives satisfaction of all constraints
  have hbinding := L.binding w (generateAllConstraints p claimed_sum challenges) qcs ligeroProof hligero
  -- Step 2: Split into sumcheck constraints + final constraint
  have ⟨h_sat, h_final⟩ := satisfiesAllConstraints_split p claimed_sum challenges w hbinding.1
  -- Step 3: Constraint satisfaction → verifierAccepts on decoded rounds
  have hva := witness_satisfies_implies_verifierAccepts p claimed_sum challenges w h_sat h_final
  -- Step 4: Decoded rounds have degree ≤ 1
  have hdeg : ∀ i, (decodeRounds w challenges i).prover_poly.natDegree ≤ 1 :=
    fun i => polyFromEvals_natDegree _ _
  -- Step 5: sumcheck_soundness_det gives root hit
  obtain ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
    sumcheck_soundness_det p claimed_sum (decodeRounds w challenges) hn (by omega) hclaim hva hdeg
  -- Step 6: The challenge in decoded rounds IS challenges i
  simp only [decodeRounds] at hdiff_eval
  exact ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩

-- ============================================================
-- Section 4: No-false-accept corollary
-- ============================================================

/-- Corollary: if Ligero binding holds, NO witness+proof pair makes the
    verifier accept a wrong claim (without hitting a root). -/
theorem longfellow_no_false_accept {n : ℕ}
    [L : LigeroScheme F (witnessSize n) (n + 1) q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (ligeroProof : L.Proof)
    (hligero : L.verify (L.commit w)
      (generateAllConstraints p claimed_sum challenges) qcs ligeroProof) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 :=
  longfellow_soundness p claimed_sum hn hclaim w challenges qcs ligeroProof hligero
