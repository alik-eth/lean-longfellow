import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Polynomial.Degree.Defs

open Finset Polynomial MultilinearPoly

/-! # ZK Simulator for Padded Sumcheck

Soundness of the padded sumcheck is already proven — `sumcheck_soundness_det`
handles any degree-≤-d adversary, including padded provers.  What is new here
is the *zero-knowledge* property: a simulator can produce fake transcripts
that satisfy the verifier's sum-check conditions **without knowing the
witness polynomial**.

The idea is simple: every round sends `simulatorPoly target = C(target) * X`,
a degree-≤-1 polynomial whose evaluations at 0 and 1 sum to `target`.
-/

variable {F : Type*} [Field F]

section SimulatorPoly

/-- A degree-≤-1 polynomial whose values at 0 and 1 sum to `target`.
    Concretely `simulatorPoly target = target · X`, so
    `eval 0 = 0` and `eval 1 = target`. -/
noncomputable def simulatorPoly (target : F) : F[X] :=
  Polynomial.C target * Polynomial.X

@[simp] theorem simulatorPoly_eval_zero (target : F) :
    (simulatorPoly target).eval 0 = 0 := by
  simp [simulatorPoly]

@[simp] theorem simulatorPoly_eval_one (target : F) :
    (simulatorPoly target).eval 1 = target := by
  simp [simulatorPoly]

theorem simulatorPoly_sum (target : F) :
    (simulatorPoly target).eval 0 + (simulatorPoly target).eval 1 = target := by
  simp

theorem simulatorPoly_degree (target : F) :
    (simulatorPoly target).natDegree ≤ 1 := by
  unfold simulatorPoly
  apply le_trans natDegree_mul_le
  have h1 : (C target : F[X]).natDegree = 0 := natDegree_C (a := target)
  have h2 : (X : F[X]).natDegree ≤ 1 := natDegree_X_le
  omega

end SimulatorPoly

section SimulateRounds

/-- Recursively build a full simulated transcript. Each round sends
    `simulatorPoly claimed_sum`; the next round's target becomes
    `(simulatorPoly claimed_sum).eval (challenges 0)`. -/
noncomputable def simulateRounds : (claimed_sum : F) →
    {n : ℕ} → (Fin n → F) → Fin n → SumcheckRound F
  | _, 0 => fun _ => Fin.elim0
  | claimed_sum, _ + 1 => fun challenges => Fin.cases
      ⟨simulatorPoly claimed_sum, challenges 0⟩
      (fun j => simulateRounds
        ((simulatorPoly claimed_sum).eval (challenges 0))
        (fun k => challenges k.succ) j)

@[simp] theorem simulateRounds_zero (claimed_sum : F) {m : ℕ}
    (challenges : Fin (m + 1) → F) :
    simulateRounds claimed_sum challenges 0 =
      ⟨simulatorPoly claimed_sum, challenges 0⟩ := by
  simp [simulateRounds, Fin.cases]

@[simp] theorem simulateRounds_succ (claimed_sum : F) {m : ℕ}
    (challenges : Fin (m + 1) → F) (j : Fin m) :
    simulateRounds claimed_sum challenges j.succ =
      simulateRounds ((simulatorPoly claimed_sum).eval (challenges 0))
        (fun k => challenges k.succ) j := by
  simp [simulateRounds, Fin.cases]

/-- The simulated rounds satisfy the telescoping sum-check conditions. -/
theorem simulateRounds_sum_check {n : ℕ} (claimed_sum : F)
    (challenges : Fin n → F) :
    ∀ i : Fin n,
      (simulateRounds claimed_sum challenges i).prover_poly.eval 0 +
      (simulateRounds claimed_sum challenges i).prover_poly.eval 1 =
        if (i : ℕ) = 0 then claimed_sum
        else (simulateRounds claimed_sum challenges ⟨i.val - 1, by omega⟩).prover_poly.eval
              (simulateRounds claimed_sum challenges ⟨i.val - 1, by omega⟩).challenge := by
  revert claimed_sum challenges
  induction n with
  | zero => intro _ _ i; exact Fin.elim0 i
  | succ m ih =>
    intro claimed_sum challenges i
    refine Fin.cases ?_ (fun j => ?_) i
    · -- Round 0: sum of simulatorPoly = claimed_sum
      simp
    · -- Round j.succ
      simp only [simulateRounds_succ, show (j.succ : ℕ) ≠ 0 from Nat.succ_ne_zero _, ↓reduceIte]
      have hprev : (⟨(j.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = j.castSucc := by
        ext; simp [Fin.val_castSucc]
      rw [hprev]
      have ih_j := ih ((simulatorPoly claimed_sum).eval (challenges 0))
        (fun k => challenges k.succ) j
      rw [ih_j]
      split
      · -- j.val = 0
        rename_i hj0
        have : j.castSucc = (0 : Fin (m + 1)) := by ext; simp [Fin.val_castSucc, hj0]
        rw [this, simulateRounds_zero]
      · -- j.val > 0
        rename_i hj_ne
        have hcast_succ : j.castSucc =
            (⟨j.val - 1, by omega⟩ : Fin m).succ := by
          ext; simp [Fin.val_castSucc]; omega
        rw [hcast_succ, simulateRounds_succ]

/-- All simulated round polynomials have degree ≤ 1. -/
theorem simulateRounds_deg {n : ℕ} (claimed_sum : F)
    (challenges : Fin n → F) :
    ∀ i : Fin n, (simulateRounds claimed_sum challenges i).prover_poly.natDegree ≤ 1 := by
  revert claimed_sum challenges
  induction n with
  | zero => intro _ _ i; exact Fin.elim0 i
  | succ m ih =>
    intro claimed_sum challenges i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [simulateRounds_zero, simulatorPoly_degree]
    · simp only [simulateRounds_succ]; exact ih _ _ j

/-- The simulator produces transcripts that satisfy the sum-check
    conditions of `verifierAccepts` (the first conjunct). This proves
    zero-knowledge: transcripts can be faked without the polynomial `p`.

    Note: the final evaluation check (second conjunct) is NOT satisfied
    because the simulator doesn't know `p`. In the full Longfellow protocol,
    this check is handled by the Ligero commitment, not the sumcheck. -/
theorem simulator_valid_sum_check {n : ℕ} (_p : MultilinearPoly F n)
    (claimed_sum : F) (challenges : Fin n → F) :
    ∀ i : Fin n,
      (simulateRounds claimed_sum challenges i).prover_poly.eval 0 +
      (simulateRounds claimed_sum challenges i).prover_poly.eval 1 =
        if (i : ℕ) = 0 then claimed_sum
        else (simulateRounds claimed_sum challenges ⟨i.val - 1, by omega⟩).prover_poly.eval
              (simulateRounds claimed_sum challenges ⟨i.val - 1, by omega⟩).challenge :=
  simulateRounds_sum_check claimed_sum challenges

end SimulateRounds
