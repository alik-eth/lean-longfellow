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

omit [DecidableEq F] [Fintype F] in
/-- The honest prover's polynomial at round `i` depends only on `cs j` for `j < i`. -/
private theorem honestProver_poly_indep :
    ∀ {n : ℕ} (p : MultilinearPoly F n) (i : Fin n) (a b : Fin n → F),
    (∀ j : Fin n, j.val < i.val → a j = b j) →
    (honestProver p a i).prover_poly = (honestProver p b i).prover_poly := by
  intro n
  induction n with
  | zero => intro _ i; exact Fin.elim0 i
  | succ m ih =>
    intro p i a b hab
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · simp [honestProver_zero]
    · simp only [honestProver_succ]
      have h0 : a 0 = b 0 := hab 0 (by show 0 < j.val + 1; omega)
      rw [h0]
      apply ih
      intro k hk
      apply hab k.succ
      show k.val + 1 < j.val + 1
      omega

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
  -- Per-round bad event using the CONCRETE diff between adversary and honest polys.
  -- The diff at round i: adversary's poly minus honest prover's poly.
  let D : Fin n → RandomChallenges F n → Polynomial F := fun i cs =>
    (adversary cs).round_polys i - (honestProver p cs i).prover_poly
  -- Per-round predicate: the concrete diff is nonzero and vanishes at cs i
  let Q : Fin n → RandomChallenges F n → Prop := fun i cs =>
    D i cs ≠ 0 ∧ (D i cs).eval (cs i) = 0
  -- Step 1: Show the bad set is contained in the union of per-round bad events
  suffices h_sub : ∀ cs, fsVerifierAccepts p claimed_sum (adversary cs) cs → ∃ i, Q i cs by
    -- Step 2: Apply union bound
    calc countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs)
        ≤ countSat (fun cs => ∃ i : Fin n, Q i cs) :=
          countSat_mono h_sub
      _ ≤ n * Fintype.card F ^ (n - 1) := by
          have h_bound : ∀ j : Fin n, countSat (Q j) ≤ Fintype.card F ^ (n - 1) := by
            intro i
            -- D i cs depends only on coords ≠ i:
            -- - adversary's poly at round i depends on cs j for j < i (non-adaptivity)
            -- - honest prover's poly at round i depends on cs j for j < i
            -- So D i cs is independent of cs i (and also of cs j for j > i).
            apply countSat_adaptive_root i (D i)
            · -- Independence: D i cs depends only on cs j for j < i, hence not on cs i
              intro cs cs' hagree
              simp only [D]
              congr 1
              · -- adversary polys: by non-adaptivity, depends on cs j for j < i
                apply h_nonadaptive cs cs' i
                intro j hj
                exact hagree j (by omega)
              · -- honest prover polys: depends on cs j for j < i
                exact honestProver_poly_indep p i cs cs'
                  (fun j hj => hagree j (by omega))
            · -- Degree bound
              intro cs
              simp only [D]
              calc ((adversary cs).round_polys i - (honestProver p cs i).prover_poly).natDegree
                  ≤ max ((adversary cs).round_polys i).natDegree
                        ((honestProver p cs i).prover_poly).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ ≤ 1 := Nat.max_le.mpr ⟨hdeg cs i, honestProver_deg_le p cs i⟩
          exact countSat_union_bound Q h_bound
  -- Step 1 proof: use sumcheck_soundness_concrete to get the concrete diff
  intro cs hfs
  have haccept : verifierAccepts p claimed_sum (toRounds (adversary cs) cs) := hfs
  have hdeg_rounds : ∀ i : Fin n, (toRounds (adversary cs) cs i).prover_poly.natDegree ≤ 1 :=
    fun i => by simp only [toRounds]; exact hdeg cs i
  obtain ⟨i, hi_ne, hi_eval⟩ :=
    sumcheck_soundness_concrete p claimed_sum (toRounds (adversary cs) cs) hn hclaim haccept hdeg_rounds
  -- The challenges of toRounds are cs
  have hchal : (fun k => (toRounds (adversary cs) cs k).challenge) = cs := by
    funext k; simp [toRounds]
  -- Rewrite hi_ne to use cs directly
  rw [hchal] at hi_ne
  -- hi_ne : (toRounds ...).prover_poly ≠ (honestProver p cs i).prover_poly
  simp only [toRounds] at hi_ne
  -- hi_ne : (adversary cs).round_polys i ≠ (honestProver p cs i).prover_poly
  refine ⟨i, ?_, ?_⟩
  · -- D i cs ≠ 0
    simp only [D]
    exact sub_ne_zero.mpr hi_ne
  · -- (D i cs).eval (cs i) = 0
    simp only [D]
    exact hi_eval

end
