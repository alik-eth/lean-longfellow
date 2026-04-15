import LeanLongfellow.Circuit.Combining
import LeanLongfellow.Sumcheck.Soundness

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] {s : ℕ}

/-! # Single-Layer Reduction

Run sumcheck on the combining polynomial to reduce a layer-i claim
`V_i(t) = c` to two claims on V_{i+1} at points (l*, r*).

Soundness follows directly from `sumcheck_soundness_det` with d = 2.
-/

/-- A single-layer reduction: sumcheck rounds for 2s variables plus
    a random challenge α for combining the two resulting claims. -/
structure LayerReduction (F : Type*) [Field F] (s : ℕ) where
  rounds : Fin (2 * s) → SumcheckRound F
  alpha : F

/-- The layer reduction verifier: run sumcheck verifier on the
    combining polynomial with claimed_sum = claimed_val. -/
def layerReductionAccepts (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_next : LayerValues F s)
    (red : LayerReduction F s) : Prop :=
  verifierAccepts (combiningPolyMLE layer t V_next) claimed_val red.rounds

/-- **Single-layer reduction soundness:** if the sumcheck verifier accepts
    but the claimed value is wrong, a challenge hit a root of a nonzero
    degree-≤-2 polynomial.

    Direct application of `sumcheck_soundness_det` with d = 2. -/
theorem layer_reduction_soundness (layer : CircuitLayer F s)
    (t : Fin s → Bool) (claimed_val : F)
    (V_curr V_next : LayerValues F s)
    (red : LayerReduction F s)
    (hs : 0 < 2 * s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g)
    (hclaim : claimed_val ≠ V_curr.table t)
    (haccept : layerReductionAccepts layer (boolToField t) claimed_val V_next red)
    (hdeg : ∀ i, (red.rounds i).prover_poly.natDegree ≤ 2) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval (red.rounds i).challenge = 0 := by
  -- Step 1: The true sum equals V_curr.table t
  have htrue : ∑ b : Fin (2 * s) → Bool,
      (combiningPolyMLE layer (boolToField t) V_next).table b = V_curr.table t := by
    simp only [combiningPolyMLE]
    exact combiningPoly_sum layer t V_curr V_next hcons
  -- Step 2: The claimed sum is wrong
  have hclaim' : claimed_val ≠ ∑ b, (combiningPolyMLE layer (boolToField t) V_next).table b := by
    rw [htrue]; exact hclaim
  -- Step 3: Apply sumcheck_soundness_det with d = 2
  exact sumcheck_soundness_det
    (combiningPolyMLE layer (boolToField t) V_next)
    claimed_val red.rounds hs (by omega) hclaim' haccept hdeg

/-- **Generalized single-layer reduction soundness:** works for any
    target `t : Fin s → F` (not just Boolean). The claimed value is
    compared against `V_curr.eval t` (MLE evaluation).

    Direct application of `sumcheck_soundness_det` with d = 2,
    using `combiningPoly_sum_general` for the true sum. -/
theorem layer_reduction_soundness_general (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_curr V_next : LayerValues F s)
    (red : LayerReduction F s)
    (hs : 0 < 2 * s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g)
    (hclaim : claimed_val ≠ V_curr.eval t)
    (haccept : layerReductionAccepts layer t claimed_val V_next red)
    (hdeg : ∀ i, (red.rounds i).prover_poly.natDegree ≤ 2) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval (red.rounds i).challenge = 0 := by
  -- Step 1: The true sum equals V_curr.eval t
  have htrue : ∑ b : Fin (2 * s) → Bool,
      (combiningPolyMLE layer t V_next).table b = V_curr.eval t := by
    simp only [combiningPolyMLE]
    exact combiningPoly_sum_general layer t V_curr V_next hcons
  -- Step 2: The claimed sum is wrong
  have hclaim' : claimed_val ≠ ∑ b, (combiningPolyMLE layer t V_next).table b := by
    rw [htrue]; exact hclaim
  -- Step 3: Apply sumcheck_soundness_det with d = 2
  exact sumcheck_soundness_det
    (combiningPolyMLE layer t V_next)
    claimed_val red.rounds hs (by omega) hclaim' haccept hdeg

-- ============================================================
-- Round-only acceptance and final evaluation check
-- ============================================================

/-- Round-only layer reduction acceptance: only the sumcheck round
    consistency conditions, WITHOUT the final evaluation check.

    In the real GKR protocol, the verifier checks round consistency at
    each intermediate layer but cannot perform the final evaluation
    check (which requires oracle access to V_{k+1}). The final
    evaluation is deferred to the next layer's reduction. -/
def layerReductionRoundsAccept (_layer : CircuitLayer F s)
    (_t : Fin s → F) (claimed_val : F)
    (_V_next : LayerValues F s)
    (red : LayerReduction F s) : Prop :=
  ∀ i : Fin (2 * s),
    (red.rounds i).prover_poly.eval 0 + (red.rounds i).prover_poly.eval 1 =
      if (i : ℕ) = 0 then claimed_val
      else (red.rounds ⟨i.val - 1, by omega⟩).prover_poly.eval
            (red.rounds ⟨i.val - 1, by omega⟩).challenge

/-- The final evaluation check for a layer reduction: the last round's
    polynomial evaluates to the combining polynomial's MLE evaluation
    at the challenge points. -/
def layerReductionFinalCheck (layer : CircuitLayer F s)
    (t : Fin s → F)
    (V_next : LayerValues F s)
    (red : LayerReduction F s)
    (_hs : 0 < 2 * s) : Prop :=
  let last : Fin (2 * s) := ⟨2 * s - 1, by omega⟩
  (red.rounds last).prover_poly.eval (red.rounds last).challenge =
    (combiningPolyMLE layer t V_next).eval (fun i => (red.rounds i).challenge)

omit [DecidableEq F] in
/-- `layerReductionAccepts` is equivalent to round acceptance AND
    the final evaluation check. -/
theorem layerReductionAccepts_iff_rounds_and_final
    (layer : CircuitLayer F s) (t : Fin s → F) (claimed_val : F)
    (V_next : LayerValues F s) (red : LayerReduction F s)
    (hs : 0 < 2 * s) :
    layerReductionAccepts layer t claimed_val V_next red ↔
    (layerReductionRoundsAccept layer t claimed_val V_next red ∧
     layerReductionFinalCheck layer t V_next red hs) := by
  simp only [layerReductionAccepts, layerReductionRoundsAccept,
    layerReductionFinalCheck, verifierAccepts]
  constructor
  · intro ⟨hrounds, hfinal⟩
    exact ⟨hrounds, hfinal hs⟩
  · intro ⟨hrounds, hfinal⟩
    exact ⟨hrounds, fun _ => hfinal⟩

omit [DecidableEq F] in
/-- `layerReductionAccepts` implies round acceptance. -/
theorem layerReductionAccepts_rounds (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_next : LayerValues F s) (red : LayerReduction F s) :
    layerReductionAccepts layer t claimed_val V_next red →
    layerReductionRoundsAccept layer t claimed_val V_next red := by
  intro ⟨hrounds, _⟩
  exact hrounds

/-- **Layer reduction propagation:** if the round checks pass, degree
    bounds hold, and the claim is wrong, then EITHER there is a root
    hit at some round OR the residual differs from the true evaluation.

    This is the key lemma for multi-layer GKR: when no root hit occurs,
    the wrong claim "survives" the sumcheck and produces a wrong residual,
    which then propagates as a wrong claim to the next layer. -/
theorem layer_reduction_propagation (layer : CircuitLayer F s)
    (t : Fin s → F) (claimed_val : F)
    (V_curr V_next : LayerValues F s)
    (red : LayerReduction F s)
    (hs : 0 < 2 * s)
    (hcons : ∀ g, layerConsistent layer V_curr V_next g)
    (hclaim : claimed_val ≠ V_curr.eval t)
    (hround : layerReductionRoundsAccept layer t claimed_val V_next red)
    (hdeg : ∀ i, (red.rounds i).prover_poly.natDegree ≤ 2) :
    (∃ i : Fin (2 * s), ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval (red.rounds i).challenge = 0) ∨
    ¬ layerReductionFinalCheck layer t V_next red hs := by
  -- By excluded middle on the final check
  by_cases hfinal : layerReductionFinalCheck layer t V_next red hs
  · -- Final check passes: full layerReductionAccepts holds
    left
    have haccept : layerReductionAccepts layer t claimed_val V_next red :=
      ⟨hround, fun _ => hfinal⟩
    exact layer_reduction_soundness_general layer t claimed_val V_curr V_next red
      hs hcons hclaim haccept hdeg
  · -- Final check fails: right disjunct
    right
    exact hfinal

-- ============================================================
-- Claim extraction and combination
-- ============================================================

/-- After the reduction, extract the two claims on V_{i+1}. -/
noncomputable def extractClaims (V_next : LayerValues F s)
    (red : LayerReduction F s) : F × F :=
  let challenges := fun k => (red.rounds k).challenge
  let l_star : Fin s → F := fun j => challenges ⟨j.val, by omega⟩
  let r_star : Fin s → F := fun j => challenges ⟨j.val + s, by omega⟩
  (V_next.eval l_star, V_next.eval r_star)

/-- Combine two claims via α:
    `next_claim = α · a + (1-α) · b` -/
def combineClaims (a b alpha : F) : F :=
  alpha * a + (1 - alpha) * b
