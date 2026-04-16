import LeanLongfellow.Circuit.Core.Reduction

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] {s : ℕ}

/-! # Multi-Layer GKR Composition

Compose single-layer sumcheck reductions across NL layers of a layered
arithmetic circuit. The central result (`gkr_chain_soundness`) models
the real GKR protocol faithfully:

* At each intermediate layer the verifier checks only sumcheck round
  consistency (`layerReductionRoundsAccept`), NOT the final polynomial
  evaluation (which would require oracle access to V_{k+1}).
* After layer k's rounds, the "residual" -- the last round polynomial
  evaluated at its challenge -- becomes an outstanding claim that links
  to layer k+1.
* At the **last** layer (k = NL-1), the verifier *does* perform the
  final evaluation check against the known input layer.

If no challenge hits a low-degree root at any layer, every outstanding
claim is correct, so the original claim must be correct.  Conversely,
a wrong original claim forces a root hit at some layer.

## Key definitions and theorems

* `gkr_chain_soundness` -- main inductive theorem with round-only
  acceptance at intermediate layers and a final check at the last layer.
* `gkr_composition` -- corollary for the case where full
  `layerReductionAccepts` (rounds + final eval) is available at every
  layer.
-/

-- ============================================================
-- Section 1: Single-layer composition (direct application)
-- ============================================================

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

    Proof: by contradiction -- if the claim were wrong,
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

-- ============================================================
-- Section 2: Inter-layer claim propagation
-- ============================================================

/-- The next layer's target point: linear interpolation between l* and r*.
    `nextTarget l* r* alpha = (1 - alpha) * l* + alpha * r*` -/
def nextTarget {s : ℕ} {F : Type*} [Field F] (l_star r_star : Fin s → F) (alpha : F) :
    Fin s → F :=
  fun j => (1 - alpha) * l_star j + alpha * r_star j

/-- Extract l* and r* challenge points from a reduction transcript. -/
def reductionPoints {s : ℕ} {F : Type*} [Field F] (red : LayerReduction F s) :
    (Fin s → F) × (Fin s → F) :=
  let challenges := fun k => (red.rounds k).challenge
  (fun j => challenges ⟨j.val, by omega⟩, fun j => challenges ⟨j.val + s, by omega⟩)

-- ============================================================
-- Section 3: GKR chain soundness
-- ============================================================

/-- **GKR chain soundness (main multi-layer composition theorem).**

If the output claim is wrong and:
* all layers have round-consistent sumcheck transcripts
  (`layerReductionRoundsAccept` -- no final eval check required),
* the LAST layer's final evaluation check passes (against the known
  input layer),
* whenever the final check at an intermediate layer k fails, the
  claim at layer k+1 is also wrong (error propagation),
* all round polynomials have degree <= 2,
* all layers are gate-consistent,

then some layer k has a sumcheck challenge that is a root of a
nonzero degree-<=2 polynomial.

This models the real GKR protocol faithfully: at each intermediate
layer the verifier checks only round consistency (NOT the final
polynomial evaluation, which would require oracle access to V_{k+1}).
The final evaluation is deferred through the chain, and only the
last layer's check (against the known input) is required.

The proof proceeds by induction on (NL - 1 - j): at layer j, either
a root hit is found via `layer_reduction_propagation`, or the final
check fails and the error propagates to layer j+1. At the last layer,
the final check closes the argument.

The `hpropagate` hypothesis captures the GKR inter-layer structure:
when the final check at layer j fails, the wrong residual -- combined
with the inter-layer linking of targets and claims -- implies the
claim at layer j+1 is also incorrect. -/
theorem gkr_chain_soundness {NL s : ℕ}
    (layers : Fin NL → CircuitLayer F s)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → F))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s)
    (hNL : 0 < NL)
    -- All layers are gate-consistent
    (hcons : ∀ k : Fin NL, ∀ g,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g)
    -- Round checks pass at all layers
    (hround : ∀ k : Fin NL,
      layerReductionRoundsAccept (layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    -- Final evaluation check at the last layer
    (hfinal_last :
      layerReductionFinalCheck
        (layers ⟨NL - 1, by omega⟩)
        (targets ⟨NL - 1, by omega⟩)
        (values ⟨NL, by omega⟩)
        (reductions ⟨NL - 1, by omega⟩)
        hs)
    -- Error propagation: if the final check at layer j fails,
    -- then the claim at layer j+1 is wrong
    (hpropagate : ∀ (j : ℕ) (hj : j < NL) (hj1 : j + 1 < NL),
      ¬ layerReductionFinalCheck (layers ⟨j, hj⟩) (targets ⟨j, hj⟩)
          (values ⟨j + 1, by omega⟩) (reductions ⟨j, hj⟩) hs →
      claimed_vals ⟨j + 1, hj1⟩ ≠
        (values ⟨j + 1, by omega⟩).eval (targets ⟨j + 1, hj1⟩))
    -- Degree bounds at all layers
    (hdeg : ∀ k : Fin NL, ∀ i,
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    -- Output claim is wrong
    (hclaim_wrong : claimed_vals ⟨0, hNL⟩ ≠ (values ⟨0, by omega⟩).eval (targets ⟨0, hNL⟩)) :
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((reductions k).rounds i).challenge = 0 := by
  -- Auxiliary: for any j < NL, if claimed_vals j is wrong, then some
  -- layer >= j has a root hit.  We induct on rem = NL - 1 - j.
  suffices aux : ∀ (rem j : ℕ) (hj : j < NL),
      rem = NL - 1 - j →
      claimed_vals ⟨j, hj⟩ ≠ (values ⟨j, by omega⟩).eval (targets ⟨j, hj⟩) →
      ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
        diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
        diff.eval ((reductions k).rounds i).challenge = 0 by
    exact aux (NL - 1) 0 hNL (by omega) hclaim_wrong
  intro rem
  induction rem with
  | zero =>
    -- Base case: j = NL - 1 (last layer)
    intro j hj hrem hclaim_j
    have hjlast : j = NL - 1 := by omega
    subst hjlast
    -- At the last layer, we have rounds + final check -> full accept
    have haccept_last : layerReductionAccepts
        (layers ⟨NL - 1, hj⟩)
        (targets ⟨NL - 1, hj⟩)
        (claimed_vals ⟨NL - 1, hj⟩)
        (values (⟨NL - 1, hj⟩ : Fin NL).succ)
        (reductions ⟨NL - 1, hj⟩) := by
      rw [layerReductionAccepts_iff_rounds_and_final _ _ _ _ _ hs]
      constructor
      · exact hround ⟨NL - 1, hj⟩
      · convert hfinal_last using 2; ext; simp [Fin.succ]; omega
    -- Apply single-layer soundness at the last layer
    -- Note: we use .castSucc / .succ to match hcons's index structure
    obtain ⟨i, diff, hne, hdeg_diff, heval⟩ :=
      layer_reduction_soundness_general
        (layers ⟨NL - 1, hj⟩) (targets ⟨NL - 1, hj⟩)
        (claimed_vals ⟨NL - 1, hj⟩)
        (values (⟨NL - 1, hj⟩ : Fin NL).castSucc)
        (values (⟨NL - 1, hj⟩ : Fin NL).succ)
        (reductions ⟨NL - 1, hj⟩) hs (hcons ⟨NL - 1, hj⟩)
        hclaim_j haccept_last (hdeg ⟨NL - 1, hj⟩)
    exact ⟨⟨NL - 1, hj⟩, i, diff, hne, hdeg_diff, heval⟩
  | succ rem' ih =>
    -- Inductive step: j < NL - 1
    intro j hj hrem hclaim_j
    -- Apply the propagation lemma at layer j
    have hprop := layer_reduction_propagation
      (layers ⟨j, hj⟩) (targets ⟨j, hj⟩) (claimed_vals ⟨j, hj⟩)
      (values ⟨j, by omega⟩) (values ⟨j + 1, by omega⟩)
      (reductions ⟨j, hj⟩)
      hs (hcons ⟨j, hj⟩) hclaim_j (hround ⟨j, hj⟩) (hdeg ⟨j, hj⟩)
    rcases hprop with ⟨i, diff, hne, hdeg_diff, heval⟩ | hno_final
    · -- Case 1: Root hit at layer j
      exact ⟨⟨j, hj⟩, i, diff, hne, hdeg_diff, heval⟩
    · -- Case 2: No root hit at layer j; final check fails, claim propagates
      have hj1 : j + 1 < NL := by omega
      -- Error propagation gives a wrong claim at j+1
      have hclaim_j1 := hpropagate j hj hj1 hno_final
      -- Apply IH at layer j+1
      exact ih (j + 1) hj1 (by omega) hclaim_j1

-- ============================================================
-- Section 4: Full GKR multi-layer composition
-- ============================================================

omit [DecidableEq F] in
/-- When full `layerReductionAccepts` holds at every layer, the error
    propagation condition is vacuously true: the "wrong final check"
    hypothesis is contradicted by the full accept (which includes the
    final check). -/
private theorem full_accepts_imply_propagation {NL s : ℕ}
    {layers : Fin NL → CircuitLayer F s}
    {values : Fin (NL + 1) → LayerValues F s}
    {targets : Fin NL → (Fin s → F)}
    {claimed_vals : Fin NL → F}
    {reductions : Fin NL → LayerReduction F s}
    {hs : 0 < 2 * s}
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    (j : ℕ) (hj : j < NL) (_hj1 : j + 1 < NL) :
    ¬ layerReductionFinalCheck (layers ⟨j, hj⟩) (targets ⟨j, hj⟩)
        (values ⟨j + 1, by omega⟩) (reductions ⟨j, hj⟩) hs →
    claimed_vals ⟨j + 1, _hj1⟩ ≠
      (values ⟨j + 1, by omega⟩).eval (targets ⟨j + 1, _hj1⟩) := by
  intro hno_final
  -- The full accept at layer j includes the final check
  have hfull := haccept ⟨j, hj⟩
  rw [layerReductionAccepts_iff_rounds_and_final _ _ _ _ _ hs] at hfull
  -- The full accept includes the final check; but it fails -> contradiction.
  exfalso; apply hno_final
  convert hfull.2 using 2

/-- Full GKR composition with F-valued targets: if the output claim is wrong
    and all layer reductions fully accept (rounds + final eval), then some
    layer k has a root hit.

    This is a corollary of `gkr_chain_soundness`: when full acceptance
    holds at every layer, the chain argument goes through with the final
    check at the last layer derived from the full accept, and the error
    propagation condition is vacuously true (the "wrong final check"
    hypothesis is contradicted by the full accept). -/
theorem gkr_composition {NL s : ℕ}
    (layers : Fin NL → CircuitLayer F s)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → F))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s)
    (hNL : 0 < NL)
    (hcons : ∀ k : Fin NL, ∀ g,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g)
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    (hdeg : ∀ k : Fin NL, ∀ i,
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    (hclaim_wrong : claimed_vals ⟨0, hNL⟩ ≠ (values ⟨0, by omega⟩).eval (targets ⟨0, hNL⟩)) :
    ∃ k : Fin NL, ∃ i : Fin (2 * s), ∃ diff : F[X],
      diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval ((reductions k).rounds i).challenge = 0 := by
  -- Extract the round checks from the full accepts
  have hround : ∀ k : Fin NL,
      layerReductionRoundsAccept (layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k) :=
    fun k => layerReductionAccepts_rounds _ _ _ _ _ (haccept k)
  -- Extract the final check at the last layer from the full accept
  have hfinal_last : layerReductionFinalCheck
      (layers ⟨NL - 1, by omega⟩) (targets ⟨NL - 1, by omega⟩)
      (values ⟨NL, by omega⟩) (reductions ⟨NL - 1, by omega⟩) hs := by
    have h := haccept ⟨NL - 1, by omega⟩
    rw [layerReductionAccepts_iff_rounds_and_final _ _ _ _ _ hs] at h
    convert h.2 using 3; simp [Fin.succ]; omega
  -- The error propagation is vacuously true (full accept contradicts
  -- the "wrong final check" hypothesis)
  exact gkr_chain_soundness layers values targets claimed_vals reductions
    hs hNL hcons hround hfinal_last
    (full_accepts_imply_propagation haccept) hdeg hclaim_wrong

/-- Contrapositive of `gkr_composition`: if no root is hit at any layer
    and all reductions accept with consistent layers, then the top-level
    claim is correct (equals MLE evaluation, not just table lookup). -/
theorem gkr_no_root_implies_correct {NL s : ℕ}
    (layers : Fin NL → CircuitLayer F s)
    (values : Fin (NL + 1) → LayerValues F s)
    (targets : Fin NL → (Fin s → F))
    (claimed_vals : Fin NL → F)
    (reductions : Fin NL → LayerReduction F s)
    (hs : 0 < 2 * s)
    (hNL : 0 < NL)
    (hcons : ∀ k : Fin NL, ∀ g,
      layerConsistent (layers k) (values k.castSucc) (values k.succ) g)
    (haccept : ∀ k : Fin NL,
      layerReductionAccepts (layers k) (targets k)
        (claimed_vals k) (values k.succ) (reductions k))
    (hdeg : ∀ k : Fin NL, ∀ i,
      ((reductions k).rounds i).prover_poly.natDegree ≤ 2)
    (hno_root : ∀ k : Fin NL, ∀ i : Fin (2 * s), ∀ diff : F[X],
      diff ≠ 0 → diff.natDegree ≤ 2 →
      diff.eval ((reductions k).rounds i).challenge ≠ 0) :
    claimed_vals ⟨0, hNL⟩ = (values ⟨0, by omega⟩).eval (targets ⟨0, hNL⟩) := by
  by_contra h
  obtain ⟨k, i, diff, h1, h2, h3⟩ := gkr_composition
    layers values targets claimed_vals reductions hs hNL hcons haccept hdeg h
  exact hno_root k i diff h1 h2 h3
