import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import Mathlib.Algebra.Polynomial.Roots

/-! # Sumcheck Soundness

This file proves two results about the soundness of the sumcheck protocol:

1. `roots_le_one_of_deg_le_one`: a nonzero polynomial of degree ≤ 1 has at most
   one root in any finite set (a special case of the Schwartz-Zippel lemma).

2. `sumcheck_soundness_det`: deterministic soundness — if the verifier accepts
   with a wrong claim, then there exists a round where the prover's polynomial
   differs from the honest polynomial, and the challenge is a root of that
   nonzero difference polynomial of degree ≤ 1.
-/

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F]

/-- A nonzero polynomial of degree ≤ 1 has at most 1 root in any finite set. -/
theorem roots_le_one_of_deg_le_one {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1)
    (S : Finset F) :
    (S.filter (fun r => p.eval r = 0)).card ≤ 1 := by
  have h1 : (S.filter (fun r => p.eval r = 0)).card ≤ p.roots.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp]
    exact Polynomial.IsRoot.def.mpr hx.2
  have h2 : p.roots.toFinset.card ≤ p.roots.card :=
    Multiset.toFinset_card_le p.roots
  have h3 : p.roots.card ≤ p.natDegree :=
    Polynomial.card_roots' p
  omega

/-- **Sumcheck deterministic soundness.**

If the verifier accepts a claimed sum that differs from the true sum,
then there exists a round `i` and a nonzero polynomial `diff` of degree ≤ 1
whose evaluation at the challenge `rounds i` is zero.

The proof proceeds by induction on `n`: if the claimed sum is wrong, either
round 0's prover polynomial differs from the honest polynomial (and the
challenge hits a root of their difference), or the claim propagates incorrectly
to the next round, and we recurse. -/
theorem sumcheck_soundness_det {n : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds)
    (hdeg : ∀ i : Fin n, (rounds i).prover_poly.natDegree ≤ 1) :
    ∃ i : Fin n, ∃ (diff : F[X]), diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (rounds i).challenge = 0 := by
  revert p claimed_sum rounds hn hclaim haccept hdeg
  induction n with
  | zero => intro _ _ _ hn; omega
  | succ m ih =>
    intro p claimed_sum rounds _hn hclaim haccept hdeg
    obtain ⟨haccept_sum, haccept_final⟩ := haccept
    -- Round 0 polynomials
    set g₀ := (rounds 0).prover_poly with hg₀_def
    set h₀ := p.sumFirstVar with hh₀_def
    set r₀ := (rounds 0).challenge with hr₀_def
    -- g₀(0) + g₀(1) = claimed_sum
    have hg₀_sum : g₀.eval 0 + g₀.eval 1 = claimed_sum := by
      have := haccept_sum (0 : Fin (m + 1)); simp at this; exact this
    -- h₀(0) + h₀(1) = ∑ p.table
    have hh₀_sum : h₀.eval 0 + h₀.eval 1 = ∑ b, p.table b := sumFirstVar_sum p
    -- g₀ ≠ h₀
    have hg₀_ne_h₀ : g₀ ≠ h₀ := by
      intro heq; exact hclaim (hg₀_sum.symm.trans (by rw [heq]; exact hh₀_sum))
    -- Difference polynomial
    set diff₀ := g₀ - h₀
    have hdiff₀_ne : diff₀ ≠ 0 := sub_ne_zero.mpr hg₀_ne_h₀
    have hdiff₀_deg : diff₀.natDegree ≤ 1 := by
      calc diff₀.natDegree ≤ max g₀.natDegree h₀.natDegree := natDegree_sub_le g₀ h₀
      _ ≤ 1 := Nat.max_le.mpr ⟨hdeg 0, sumFirstVar_natDegree_le p⟩
    by_cases hdiff₀_eval : diff₀.eval r₀ = 0
    · exact ⟨0, diff₀, hdiff₀_ne, hdiff₀_deg, hdiff₀_eval⟩
    · -- g₀(r₀) ≠ h₀(r₀), so the propagated claim is wrong
      have heval_ne : g₀.eval r₀ ≠ h₀.eval r₀ := by
        intro heq; exact hdiff₀_eval (by simp [diff₀, Polynomial.eval_sub, heq])
      set reduced := p.partialEvalFirst r₀
      have hclaim' : g₀.eval r₀ ≠ ∑ b, reduced.table b := by
        rwa [← show h₀.eval r₀ = ∑ b, reduced.table b from
          (partialEval_table_sum p r₀).symm]
      -- Build verifierAccepts for the reduced protocol
      set rounds' : Fin m → SumcheckRound F := fun j => rounds j.succ
      have hdeg' : ∀ i : Fin m, (rounds' i).prover_poly.natDegree ≤ 1 := fun i => hdeg i.succ
      -- Simplify haccept_final
      have hfinal : (rounds ⟨m, by omega⟩).prover_poly.eval
            (rounds ⟨m, by omega⟩).challenge =
          p.eval (fun i => (rounds i).challenge) :=
        haccept_final (by omega)
      -- Build the sum-check condition for the reduced protocol
      have haccept'_sum : ∀ i : Fin m,
          (rounds' i).prover_poly.eval 0 + (rounds' i).prover_poly.eval 1 =
            if (i : ℕ) = 0 then g₀.eval r₀
            else (rounds' ⟨i.val - 1, by omega⟩).prover_poly.eval
                  (rounds' ⟨i.val - 1, by omega⟩).challenge := by
        intro i
        have horig := haccept_sum i.succ
        simp only [show (i.succ : ℕ) ≠ 0 from Nat.succ_ne_zero _, ↓reduceIte] at horig
        -- horig: rounds(i.succ).eval 0 + .eval 1 = rounds(⟨i.succ-1, _⟩).eval ...
        -- ⟨i.succ.val - 1, _⟩ = ⟨i.val, _⟩
        have hfin : (⟨(i.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = ⟨i.val, by omega⟩ := by
          ext; simp
        rw [hfin] at horig
        -- horig is now: (rounds i.succ)... = (rounds ⟨i.val, _⟩)...
        -- rounds' i = rounds i.succ, so LHS matches
        -- For RHS:
        split
        · -- i.val = 0
          rename_i hi0
          have : (⟨i.val, by omega⟩ : Fin (m + 1)) = 0 := by ext; exact hi0
          rw [this] at horig
          exact horig
        · -- i.val > 0
          rename_i hi_ne
          -- rounds' ⟨i.val-1, _⟩ = rounds ⟨i.val, _⟩ (since ⟨i.val-1, _⟩.succ = ⟨i.val, _⟩)
          -- This is definitionally true: rounds' ⟨i.val-1, _⟩ = rounds ⟨i.val-1, _⟩.succ
          -- and ⟨i.val-1, _⟩.succ.val = i.val-1+1 = i.val
          -- But ⟨i.val-1, _⟩.succ has different proof term than ⟨i.val, _⟩ in Fin (m+1)
          -- So use congr
          have : (⟨i.val - 1, by omega⟩ : Fin m).succ = (⟨i.val, by omega⟩ : Fin (m + 1)) := by
            ext; simp; omega
          simp only [rounds'] at horig ⊢
          rw [this]
          exact horig
      -- Build the final evaluation check for the reduced protocol
      have haccept'_final : ∀ (hm : 0 < m),
          let last : Fin m := ⟨m - 1, by omega⟩
          (rounds' last).prover_poly.eval (rounds' last).challenge =
            reduced.eval (fun i => (rounds' i).challenge) := by
        intro hm
        simp only
        -- rounds' ⟨m-1, _⟩ = rounds ⟨m, _⟩
        have hlast : (⟨m - 1, by omega⟩ : Fin m).succ = (⟨m, by omega⟩ : Fin (m + 1)) := by
          ext; simp; omega
        simp only [rounds'] at hfinal ⊢
        rw [hlast, hfinal, partialEvalFirst_eval]
        congr 1; funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.cons_zero, hr₀_def]
        · simp [Fin.cons_succ]
      have haccept' : verifierAccepts reduced (g₀.eval r₀) rounds' :=
        ⟨haccept'_sum, haccept'_final⟩
      -- Apply IH or handle base case
      cases m with
      | zero =>
        -- n = 1, m = 0: contradiction
        -- The verifier accepted with 0 reduced rounds, but claim is wrong
        exfalso; apply hclaim'
        -- g₀.eval r₀ = p.eval (fun i => rounds(i).challenge) (from hfinal)
        -- ∑ reduced.table = reduced.eval Fin.elim0 = p.eval (Fin.cons r₀ Fin.elim0)
        have h0sum : ∀ (q : MultilinearPoly F 0) (x : Fin 0 → F),
            ∑ b : Fin 0 → Bool, q.table b = q.eval x := by
          intro q x
          have hsub : ∀ (b : Fin 0 → Bool), b = Fin.elim0 :=
            fun b => funext (fun i => Fin.elim0 i)
          simp only [MultilinearPoly.eval, lagrangeBasis]
          rw [Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb),
              Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb)]
          simp [Finset.prod_empty]
        rw [h0sum reduced Fin.elim0, partialEvalFirst_eval]
        -- Goal: g₀.eval r₀ = p.eval (Fin.cons r₀ Fin.elim0)
        -- hfinal: rounds(⟨0, _⟩).eval ... = p.eval (...)
        -- Unfold g₀ and r₀ to match hfinal
        simp only [g₀, r₀] at hfinal ⊢
        convert hfinal using 1
      | succ m' =>
        obtain ⟨j, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
          ih reduced (g₀.eval r₀) rounds' (by omega) hclaim' haccept' hdeg'
        exact ⟨j.succ, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩
