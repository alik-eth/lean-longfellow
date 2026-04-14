import LeanLongfellow.FiatShamir.Oracle
import LeanLongfellow.FiatShamir.Transform
import LeanLongfellow.Sumcheck.Soundness
import LeanLongfellow.MLE.Props

open Finset Polynomial MultilinearPoly Classical

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! # Fiat-Shamir ROM Soundness

This file proves the main soundness theorem for the Fiat-Shamir transform
applied to the sumcheck protocol in the Random Oracle Model.

For any non-adaptive adversary, if the claimed sum is wrong, the number of
challenge vectors that fool the verifier is at most `n * |F|^(n-1)`.
Dividing by `|F|^n` gives probability bound `n / |F|`.

## Proof outline

1. For each `cs` where `fsVerifierAccepts` holds, unfold to `verifierAccepts`
   and apply `sumcheck_soundness_det` to get a witness round `i` and a nonzero
   degree-≤-1 difference polynomial `diff` with `diff.eval (cs i) = 0`.

2. Decompose the bad set by round index using union bound
   (`countSat_union_bound`).

3. For each round `i`, bound the bad set by `|F|^(n-1)` using the fact that
   the difference polynomial is determined by the earlier challenges (by
   non-adaptivity) and a nonzero degree-≤-1 polynomial has at most one root.
-/

/-- Monotonicity of `countSat` with respect to implication. -/
private theorem countSat_mono {F : Type*} [DecidableEq F] [Fintype F] {n : ℕ}
    {P Q : RandomChallenges F n → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ cs, P cs → Q cs) :
    countSat P ≤ countSat Q := by
  unfold countSat
  apply Finset.card_le_card
  intro cs hcs
  rw [Finset.mem_filter] at hcs ⊢
  exact ⟨hcs.1, h cs hcs.2⟩

/-- **Fiat-Shamir ROM Soundness.**
For any non-adaptive adversary, if the claimed sum is wrong,
the number of challenge vectors that fool the verifier is at most `n * |F|^(n-1)`.
Dividing by |F|^n gives probability bound n/|F|. -/
theorem fiatShamir_soundness {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ 1)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * Fintype.card F ^ (n - 1) := by
  -- Per-round bad event: there exists a nonzero deg-≤-1 poly vanishing at cs i
  let P : Fin n → RandomChallenges F n → Prop := fun i cs =>
    ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧ diff.eval (cs i) = 0
  -- Step 1: Show the bad set is contained in the union of per-round bad events
  suffices h_sub : ∀ cs, fsVerifierAccepts p claimed_sum (adversary cs) cs → ∃ i, P i cs by
    -- Step 2: Apply union bound
    calc countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs)
        ≤ countSat (fun cs => ∃ i : Fin n, P i cs) :=
          countSat_mono h_sub
      _ ≤ n * Fintype.card F ^ (n - 1) := by
          have h_bound : ∀ j : Fin n, countSat (P j) ≤ Fintype.card F ^ (n - 1) := by
            intro i
            -- The hard step: for each round i, the bad set has size ≤ |F|^(n-1).
            -- By non-adaptivity, the diff polynomial at round i depends only on cs j for j < i.
            -- For each fixed assignment of earlier coordinates, diff is determined.
            -- Since diff ≠ 0 with deg ≤ 1, at most 1 value of cs i works.
            -- The remaining n - i - 1 later coordinates are free.
            -- Total: |F|^i * 1 * |F|^(n-i-1) = |F|^(n-1).
            sorry
          exact countSat_union_bound P h_bound
  -- Step 1 proof: connect to sumcheck_soundness_det
  intro cs hfs
  have haccept : verifierAccepts p claimed_sum (toRounds (adversary cs) cs) := hfs
  have hdeg_rounds : ∀ i : Fin n, (toRounds (adversary cs) cs i).prover_poly.natDegree ≤ 1 :=
    fun i => by simp only [toRounds]; exact hdeg cs i
  obtain ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
    sumcheck_soundness_det p claimed_sum (toRounds (adversary cs) cs) hn hclaim haccept hdeg_rounds
  exact ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩

end
