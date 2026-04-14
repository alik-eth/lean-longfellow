import LeanLongfellow.GKR.Combining
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {k depth : ℕ}

omit [Fintype F] in
/-- If the sumcheck verifier accepts the combining polynomial with claimed sum
    V[j](g*), but the layer is NOT consistent at g*, then some challenge
    hits a root of a nonzero degree-≤-1 polynomial. -/
theorem layer_reduction_soundness
    (circuit : LayeredCircuit F k depth) (j : Fin depth)
    (gStar : Fin k → F) (rounds : Fin (2 * k) → SumcheckRound F)
    (hk : 0 < 2 * k)
    (haccept : verifierAccepts (combiningPoly circuit j gStar)
      ((circuit.wires (Fin.castSucc j)).eval gStar) rounds)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_inconsistent : ¬ layerConsistentAt circuit j gStar) :
    ∃ i, ∃ d : F[X], d ≠ 0 ∧ d.natDegree ≤ 1 ∧
      d.eval (rounds i).challenge = 0 := by
  have hclaim : (circuit.wires (Fin.castSucc j)).eval gStar ≠
      ∑ b, (combiningPoly circuit j gStar).table b := by
    intro heq
    exact h_inconsistent heq
  exact sumcheck_soundness_det _ _ _ hk hclaim haccept hdeg

omit [DecidableEq F] [Fintype F] in
/-- If a layer is inconsistent, there exists a Boolean gate where it fails. -/
theorem random_gstar_detects (circuit : LayeredCircuit F k depth)
    (j : Fin depth) (h_inconsistent : ¬ layerConsistent circuit j) :
    ∃ g : Fin k → Bool, ¬ layerConsistentAt circuit j (boolToField g) :=
  not_forall.mp h_inconsistent
