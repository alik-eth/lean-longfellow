import LeanLongfellow.Circuit.Reduction

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] {s : ℕ}

/-! # Multi-Layer Composition

Compose single-layer reductions across NL layers. The key result:
if no challenge hits a degree-≤-2 root anywhere, the original claim is correct.
-/

/-- Multi-layer soundness: if the top-level claim is wrong and layer 0's
    reduction accepts, a root is hit at layer 0. Immediate from
    `layer_reduction_soundness`. -/
theorem multi_layer_soundness {NL : ℕ}
    (layers : Fin NL → CircuitLayer F s)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → Bool))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s)
    (hNL : 0 < NL)
    (hcons : ∀ k : Fin NL, ∀ g,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g)
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (layers k) (boolToField (targets k))
        (claimed_vals k) (values k.succ) (reductions k))
    (hdeg : ∀ k : Fin NL, ∀ i,
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    (hclaim_wrong : claimed_vals ⟨0, hNL⟩ ≠ (values ⟨0, by omega⟩).table (targets ⟨0, hNL⟩)) :
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((reductions k).rounds i).challenge = 0 := by
  -- Direct: apply layer_reduction_soundness at layer 0
  obtain ⟨i, diff, h1, h2, h3⟩ := layer_reduction_soundness
    (layers ⟨0, hNL⟩) (targets ⟨0, hNL⟩) (claimed_vals ⟨0, hNL⟩)
    (values ⟨0, by omega⟩) (values ⟨1, by omega⟩) (reductions ⟨0, hNL⟩)
    hs (hcons ⟨0, hNL⟩) hclaim_wrong (haccept ⟨0, hNL⟩) (hdeg ⟨0, hNL⟩)
  exact ⟨⟨0, hNL⟩, i, diff, h1, h2, h3⟩

/-- Contrapositive: if no root is hit at any layer and all reductions
    accept with consistent layers, then the top-level claim is correct.

    Proof: by contradiction — if the claim were wrong,
    `layer_reduction_soundness` at layer 0 would give a root hit. -/
theorem no_root_implies_correct {NL : ℕ}
    (layers : Fin NL → CircuitLayer F s)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → Bool))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s)
    (hNL : 0 < NL)
    (hcons : ∀ k : Fin NL, ∀ g,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g)
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (layers k) (boolToField (targets k))
        (claimed_vals k) (values k.succ) (reductions k))
    (hdeg : ∀ k : Fin NL, ∀ i,
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s), ∀ diff : F[X],
      diff ≠ 0 → diff.natDegree ≤ 2 →
      diff.eval ((reductions k).rounds i).challenge ≠ 0) :
    claimed_vals ⟨0, hNL⟩ = (values ⟨0, by omega⟩).table (targets ⟨0, hNL⟩) := by
  by_contra h
  obtain ⟨k, i, diff, h1, h2, h3⟩ := multi_layer_soundness
    layers values targets claimed_vals reductions hs hNL hcons haccept hdeg h
  exact hno_root k i diff h1 h2 h3
