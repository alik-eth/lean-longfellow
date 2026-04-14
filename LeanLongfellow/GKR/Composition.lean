import LeanLongfellow.GKR.LayerReduction
import LeanLongfellow.GKR.Pad
import LeanLongfellow.FiatShamir.Oracle

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

noncomputable section

/-- For a fixed inconsistent layer, the bad sumcheck challenges are bounded. -/
theorem gkr_per_layer_bound (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (gStar : Fin k → F)
    (hk : 0 < 2 * k)
    (h_inconsistent : ¬ layerConsistentAt circuit j gStar)
    (adversary : RandomChallenges F (2 * k) → Fin (2 * k) → SumcheckRound F)
    (hdeg : ∀ cs i, (adversary cs i).prover_poly.natDegree ≤ 1) :
    countSat (fun cs =>
      layerVerifierAccepts circuit j gStar (adversary cs)) ≤
      (2 * k) * Fintype.card F ^ (2 * k - 1) := by
  sorry
end
