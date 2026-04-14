import LeanLongfellow.FiatShamir.Oracle
import LeanLongfellow.FiatShamir.Soundness
import LeanLongfellow.Ligero.FiatShamir
import LeanLongfellow.Circuit.Probability

open Finset

/-! # End-to-End Probabilistic Soundness Composition

This file composes the individual probabilistic soundness bounds from
the Longfellow proof system into a single end-to-end error bound via
the union bound.

## Components

The Longfellow proof system has four sources of soundness error:

1. **GKR/Sumcheck** (per layer): each of `NL` circuit layers runs a
   sumcheck with `2*s` rounds. By `fiatShamir_soundness`, each layer
   contributes at most `(2*s) * (d * |F|^(2*s - 1))` bad challenges.

2. **Ligero linear test**: if the witness violates some linear
   constraint, the single-challenge test passes on at most
   `|F|^(m-1)` out of `|F|^m` challenge vectors (`linearTest_prob_soundness`).

3. **Ligero quadratic test**: if some quadratic constraint is violated,
   the single-challenge test passes on at most `|F|^(q-1)` out of
   `|F|^q` challenge vectors (`quadTest_prob_soundness`).

4. **Ligero LDT**: if some tableau row is not a codeword, the low-degree
   test detects this with probability related to the RS distance.

## Main result

`longfellow_total_error`: if each component has a bounded error count,
the total error count is bounded by their sum. This is the master
composition theorem connecting all Longfellow subsystems.

The proof is a direct application of the union bound: the bad event
(verifier accepts a wrong claim) implies at least one component fails,
so `countSat P_bad <= sum of individual countSat bounds`.
-/

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

-- ============================================================
-- Section 1: Error parameter structure
-- ============================================================

/-- Parameters describing the error budget of a Longfellow proof.
    Each field is the *numerator* of the error probability for one
    component; the denominator is the total challenge space size. -/
structure LongfellowErrorParams where
  /-- Number of GKR/sumcheck layers -/
  num_layers : ℕ
  /-- Per-layer sumcheck error count bound -/
  sumcheck_error_per_layer : ℕ
  /-- Ligero linear test error count bound -/
  ligero_linear_error : ℕ
  /-- Ligero quadratic test error count bound -/
  ligero_quad_error : ℕ
  /-- Ligero LDT error count bound -/
  ligero_ldt_error : ℕ

/-- Total error count: sum of all component error bounds. -/
def LongfellowErrorParams.total (p : LongfellowErrorParams) : ℕ :=
  p.num_layers * p.sumcheck_error_per_layer +
  p.ligero_linear_error +
  p.ligero_quad_error +
  p.ligero_ldt_error

-- ============================================================
-- Section 2: Abstract union bound composition
-- ============================================================

omit [Field F] in
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

omit [Field F] in
/-- **End-to-end composition**: if each component has a bounded error
    count, the total error count is bounded by their sum.

    This is the master theorem connecting all Longfellow components:
    sumcheck (per layer) + Ligero linear + Ligero quadratic + Ligero LDT.

    The theorem is parametric in the challenge space dimension `n` and
    takes the four bad-event predicates and their individual bounds as
    hypotheses. The conclusion follows from the union bound. -/
theorem longfellow_total_error {n : ℕ}
    {NL : ℕ} {E_sc E_lin E_quad E_ldt : ℕ}
    -- Per-layer sumcheck bad event
    (P_sumcheck : Fin NL → RandomChallenges F n → Prop)
    [∀ k, DecidablePred (P_sumcheck k)]
    -- Ligero test bad events
    (P_linear : RandomChallenges F n → Prop) [DecidablePred P_linear]
    (P_quad : RandomChallenges F n → Prop) [DecidablePred P_quad]
    (P_ldt : RandomChallenges F n → Prop) [DecidablePred P_ldt]
    -- Overall bad event
    (P_bad : RandomChallenges F n → Prop) [DecidablePred P_bad]
    -- Individual bounds
    (sumcheck_bound : ∀ k : Fin NL, countSat (P_sumcheck k) ≤ E_sc)
    (linear_bound : countSat P_linear ≤ E_lin)
    (quad_bound : countSat P_quad ≤ E_quad)
    (ldt_bound : countSat P_ldt ≤ E_ldt)
    -- Decomposition: the bad event implies one of the components fails
    (h_decomp : ∀ cs, P_bad cs →
      (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) :
    countSat P_bad ≤ NL * E_sc + E_lin + E_quad + E_ldt := by
  -- Step 1: Reduce to union of four top-level events
  -- Encode the four event families as Fin 4 predicates, but it's cleaner
  -- to do the union bound manually in two stages.
  --
  -- First, bound P_bad by the disjunction
  have h_sub : countSat P_bad ≤
      countSat (fun cs => (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) :=
    countSat_mono' h_decomp
  -- Step 2: Bound the disjunction by summing individual bounds
  -- We split the disjunction into sumcheck part and Ligero parts
  have h_disj : countSat (fun cs =>
      (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) ≤
      countSat (fun cs => ∃ k, P_sumcheck k cs) +
      countSat P_linear + countSat P_quad + countSat P_ldt := by
    unfold countSat
    -- Filter ⊆ four-way union
    have hsub : univ.filter (fun cs =>
        (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) ⊆
        (univ.filter (fun cs => ∃ k, P_sumcheck k cs)) ∪
        (univ.filter P_linear) ∪
        (univ.filter P_quad) ∪
        (univ.filter P_ldt) := by
      intro cs hcs
      rw [Finset.mem_filter] at hcs
      rw [Finset.mem_union, Finset.mem_union, Finset.mem_union]
      rcases hcs.2 with h_sc | h_lin | h_quad | h_ldt
      · left; left; left; exact Finset.mem_filter.mpr ⟨hcs.1, h_sc⟩
      · left; left; right; exact Finset.mem_filter.mpr ⟨hcs.1, h_lin⟩
      · left; right; exact Finset.mem_filter.mpr ⟨hcs.1, h_quad⟩
      · right; exact Finset.mem_filter.mpr ⟨hcs.1, h_ldt⟩
    -- Card of union ≤ sum of cards (iterated card_union_le)
    calc (univ.filter _).card
        ≤ ((univ.filter (fun cs => ∃ k, P_sumcheck k cs)) ∪
           (univ.filter P_linear) ∪
           (univ.filter P_quad) ∪
           (univ.filter P_ldt)).card := Finset.card_le_card hsub
      _ ≤ ((univ.filter (fun cs => ∃ k, P_sumcheck k cs)) ∪
           (univ.filter P_linear) ∪
           (univ.filter P_quad)).card +
          (univ.filter P_ldt).card := Finset.card_union_le _ _
      _ ≤ (((univ.filter (fun cs => ∃ k, P_sumcheck k cs)) ∪
            (univ.filter P_linear)).card +
           (univ.filter P_quad).card) +
          (univ.filter P_ldt).card := by
            gcongr
            exact Finset.card_union_le _ _
      _ ≤ ((univ.filter (fun cs => ∃ k, P_sumcheck k cs)).card +
           (univ.filter P_linear).card +
          (univ.filter P_quad).card) +
          (univ.filter P_ldt).card := by
            gcongr
            exact Finset.card_union_le _ _
  -- Step 3: Bound the sumcheck union by NL * E_sc
  have h_sc_union : countSat (fun cs => ∃ k, P_sumcheck k cs) ≤ NL * E_sc :=
    countSat_union_bound P_sumcheck sumcheck_bound
  -- Step 4: Combine all bounds
  calc countSat P_bad
      ≤ countSat (fun cs => (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) := h_sub
    _ ≤ countSat (fun cs => ∃ k, P_sumcheck k cs) +
        countSat P_linear + countSat P_quad + countSat P_ldt := h_disj
    _ ≤ NL * E_sc + E_lin + E_quad + E_ldt := by linarith

-- ============================================================
-- Section 3: Concrete instantiation with existing bounds
-- ============================================================

open Classical in
/-- Concrete error bound for the Ligero linear test, restated in a
    form convenient for composition. If the witness violates some
    linear constraint, the single-challenge linear test passes on
    at most `|F|^(m-1)` challenge vectors. -/
noncomputable def ligero_linear_error_bound {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h_viol : ¬ satisfiesLinear w lcs) :
    countSat (fun alpha : Fin m → F =>
      linearTestSingleChallenge w lcs alpha) ≤
      Fintype.card F ^ (m - 1) :=
  linearTest_prob_soundness w lcs h_viol

open Classical in
/-- Concrete error bound for the Ligero quadratic test, restated in a
    form convenient for composition. If some quadratic constraint is
    violated, the single-challenge quadratic test passes on at most
    `|F|^(q-1)` challenge vectors. -/
noncomputable def ligero_quad_error_bound {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ ∀ i, satisfiesQuad w (qcs i)) :
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
      Fintype.card F ^ (q - 1) :=
  quadTest_prob_soundness w qcs h_viol

open Classical in
/-- Concrete per-layer GKR error bound, restated for composition.
    Each layer's sumcheck with `2*s` rounds and degree-2 polynomials
    has at most `(2*s) * (2 * |F|^(2*s - 1))` bad challenge vectors. -/
theorem gkr_layer_error_bound {s : ℕ}
    (p : MultilinearPoly F (2 * s)) (claimed_sum : F)
    (hs : 0 < 2 * s)
    (hclaim : claimed_sum ≠ ∑ b : Fin (2 * s) → Bool, p.table b)
    (adversary : RandomChallenges F (2 * s) → FiatShamirProof F (2 * s))
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ 2)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F (2 * s)) (i : Fin (2 * s)),
      (∀ j : Fin (2 * s), j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      (2 * s) * (2 * Fintype.card F ^ (2 * s - 1)) :=
  layer_error_bound p claimed_sum hs hclaim adversary hdeg h_nonadaptive
