import LeanLongfellow.GKR.LayerReduction
import LeanLongfellow.GKR.Pad
import LeanLongfellow.FiatShamir.Oracle
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly Classical

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k depth : ℕ}

/-- Per-layer GKR verifier: check the combining polynomial sumcheck. -/
def layerVerifierAccepts (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (rounds : Fin (2 * k) → SumcheckRound F) : Prop :=
  verifierAccepts (combiningPoly circuit j gStar)
    ((circuit.wires (Fin.castSucc j)).eval gStar) rounds

/-- Full GKR verifier: all per-layer checks pass. -/
def gkrVerifierAccepts (circuit : LayeredCircuit F k depth)
    (gStars : Fin depth → Fin k → F)
    (allRounds : Fin depth → Fin (2 * k) → SumcheckRound F) : Prop :=
  ∀ j, layerVerifierAccepts circuit j (gStars j) (allRounds j)

omit [Fintype F] in
/-- Deterministic GKR soundness: if GKR accepts and a specific layer is
    inconsistent at the given g*, then some challenge in that layer's
    sumcheck is a root hit of a nonzero degree-le-1 polynomial. -/
theorem gkr_soundness_det (circuit : LayeredCircuit F k depth)
    (gStars : Fin depth → Fin k → F)
    (allRounds : Fin depth → Fin (2 * k) → SumcheckRound F)
    (hk : 0 < 2 * k)
    (j_bad : Fin depth)
    (h_inconsistent : ¬ layerConsistentAt circuit j_bad (gStars j_bad))
    (haccept : gkrVerifierAccepts circuit gStars allRounds)
    (hdeg : ∀ j i, (allRounds j i).prover_poly.natDegree ≤ 1) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (allRounds j_bad i).challenge = 0 := by
  have h_layer := haccept j_bad
  exact layer_reduction_soundness circuit j_bad (gStars j_bad) (allRounds j_bad)
    hk h_layer (hdeg j_bad) h_inconsistent

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

noncomputable section

/-- Monotonicity of `countSat` with respect to implication. -/
private theorem countSat_mono' {n : ℕ}
    {P Q : RandomChallenges F n → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ cs, P cs → Q cs) :
    countSat P ≤ countSat Q := by
  unfold countSat
  apply Finset.card_le_card
  intro cs hcs
  rw [Finset.mem_filter] at hcs ⊢
  exact ⟨hcs.1, h cs hcs.2⟩

/-- For a fixed inconsistent layer, the number of challenge vectors that fool
    the verifier is at most `(2*k) * |F|^(2*k-1)`.

    The adversary is non-adaptive: the prover polynomial at round `i` depends
    only on challenges `cs j` for `j < i`, matching the Fiat-Shamir pattern. -/
theorem gkr_per_layer_bound (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (hk : 0 < 2 * k)
    (h_inconsistent : ¬ layerConsistentAt circuit j gStar)
    (adversary : RandomChallenges F (2 * k) → Fin (2 * k) → SumcheckRound F)
    (hdeg : ∀ cs i, (adversary cs i).prover_poly.natDegree ≤ 1)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F (2 * k)) (i : Fin (2 * k)),
      (∀ j : Fin (2 * k), j.val < i.val → cs j = cs' j) →
      (adversary cs i).prover_poly = (adversary cs' i).prover_poly)
    (h_challenge : ∀ cs i, (adversary cs i).challenge = cs i) :
    countSat (fun cs =>
      layerVerifierAccepts circuit j gStar (adversary cs)) ≤
      (2 * k) * Fintype.card F ^ (2 * k - 1) := by
  -- The combining polynomial for this layer
  set p := combiningPoly circuit j gStar with hp_def
  -- The claimed sum
  set claimed := (circuit.wires (Fin.castSucc j)).eval gStar with hclaimed_def
  -- The claimed sum is wrong (from inconsistency)
  have hclaim : claimed ≠ ∑ b, p.table b := by
    intro heq; exact h_inconsistent heq
  -- The concrete diff between adversary and honest prover
  let D : Fin (2 * k) → RandomChallenges F (2 * k) → Polynomial F := fun i cs =>
    (adversary cs i).prover_poly - (honestProver p cs i).prover_poly
  -- Per-round predicate: the concrete diff is nonzero and vanishes at cs i
  let Q : Fin (2 * k) → RandomChallenges F (2 * k) → Prop := fun i cs =>
    D i cs ≠ 0 ∧ (D i cs).eval (cs i) = 0
  -- Step 1: Show the bad set is contained in the union of per-round bad events
  suffices h_sub : ∀ cs, layerVerifierAccepts circuit j gStar (adversary cs) → ∃ i, Q i cs by
    -- Step 2: Apply union bound
    calc countSat (fun cs => layerVerifierAccepts circuit j gStar (adversary cs))
        ≤ countSat (fun cs => ∃ i : Fin (2 * k), Q i cs) :=
          countSat_mono' h_sub
      _ ≤ (2 * k) * Fintype.card F ^ (2 * k - 1) := by
          have h_bound : ∀ r : Fin (2 * k), countSat (Q r) ≤ Fintype.card F ^ (2 * k - 1) := by
            intro i
            apply countSat_adaptive_root i (D i)
            · -- Independence: D i cs depends only on cs j for j < i, hence not on cs i
              intro cs cs' hagree
              simp only [D]
              congr 1
              · -- adversary polys: by non-adaptivity, depends on cs j for j < i
                apply h_nonadaptive cs cs' i
                intro r hr
                exact hagree r (by omega)
              · -- honest prover polys: depends on cs j for j < i
                exact honestProver_poly_indep p i cs cs'
                  (fun r hr => hagree r (by omega))
            · -- Degree bound
              intro cs
              simp only [D]
              calc ((adversary cs i).prover_poly - (honestProver p cs i).prover_poly).natDegree
                  ≤ max ((adversary cs i).prover_poly).natDegree
                        ((honestProver p cs i).prover_poly).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ ≤ 1 := Nat.max_le.mpr ⟨hdeg cs i, honestProver_deg_le p cs i⟩
          exact countSat_union_bound Q h_bound
  -- Step 1 proof: use sumcheck_soundness_concrete to get the concrete diff
  intro cs haccept
  -- layerVerifierAccepts unfolds to verifierAccepts p claimed (adversary cs)
  have hva : verifierAccepts p claimed (adversary cs) := haccept
  have hdeg_rounds : ∀ i : Fin (2 * k), (adversary cs i).prover_poly.natDegree ≤ 1 :=
    fun i => hdeg cs i
  obtain ⟨i, hi_ne, hi_eval⟩ :=
    sumcheck_soundness_concrete p claimed (adversary cs) hk hclaim hva hdeg_rounds
  -- The challenges of adversary cs are cs (by h_challenge)
  have hchal : (fun r => (adversary cs r).challenge) = cs := by
    funext r; exact h_challenge cs r
  -- Rewrite to use cs directly
  rw [hchal] at hi_ne hi_eval
  have hci : (adversary cs i).challenge = cs i := h_challenge cs i
  rw [hci] at hi_eval
  refine ⟨i, ?_, ?_⟩
  · -- D i cs ≠ 0
    simp only [D]
    exact sub_ne_zero.mpr hi_ne
  · -- (D i cs).eval (cs i) = 0
    simp only [D]
    exact hi_eval

end
