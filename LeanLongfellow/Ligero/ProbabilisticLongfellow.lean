import LeanLongfellow.Ligero.ProbabilisticBinding
import LeanLongfellow.Ligero.Longfellow
import LeanLongfellow.Ligero.ProbabilisticE2E

set_option autoImplicit false

/-! # Probabilistic Longfellow Soundness

This file bridges the gap between the probabilistic Ligero verifier
(`niLigeroVerify`) and the deterministic Longfellow soundness chain.

## The composition gap

Two parallel soundness paths exist in the codebase:

1. **Deterministic path**: `longfellow_soundness` uses an abstract
   `LigeroScheme` with deterministic binding (`verify → satisfiesAll` always).
2. **Probabilistic path**: `niLigeroVerify` gives `satisfiesAll ∨ BadEvent`
   via `niLigero_binding_or_bad`, with error bounds from
   `niLigero_combined_error`.

This file composes them: if `niLigeroVerify` accepts with good challenges
(not in the bad set), then `satisfiesAll` holds, and `longfellow_soundness`'s
conclusion (sumcheck root hit for a wrong claim) follows.

## Main results

- `probabilistic_longfellow_soundness`: if `niLigeroVerify` accepts and
  the challenges avoid the bad set, and the claimed sum is wrong, then
  a sumcheck challenge hit a polynomial root.

- `probabilistic_longfellow_error_bound`: if the witness does not satisfy
  all constraints, either the linear or quadratic bad set is small,
  bounding the probability of fooling the verifier.

- `probabilistic_longfellow_full_composition`: wires `longfellow_total_error`
  into the composition for a single end-to-end error bound.

- `probabilistic_longfellow_capstone`: the EndToEnd capstone conclusion
  holds whenever the combined bad event does not occur.
-/

open Finset Polynomial MultilinearPoly Classical

-- ============================================================
-- Section 1: Bridge — NI Ligero + good challenges → root hit
-- ============================================================

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

omit [Fintype F] in
/-- **Probabilistic Longfellow soundness:** if the NI Ligero verifier
    accepts with good challenges (not in the bad set for either the
    linear or quadratic test), and the claimed sum is wrong, then a
    sumcheck challenge hit a root of a nonzero degree-le-1 polynomial.

    This composes:
    1. `niLigero_contrapositive` — good challenges + acceptance → `satisfiesAll`
    2. `satisfiesAll` → split into sumcheck + final constraints
    3. `witness_satisfies_implies_verifierAccepts` — constraint satisfaction →
       `verifierAccepts` on decoded rounds
    4. `sumcheck_soundness_det` — wrong claim + verifierAccepts → root hit -/
theorem probabilistic_longfellow_soundness {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    -- NI Ligero accepted
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    -- Good challenges: if constraints were violated, the tests would catch it
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges) niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 := by
  -- Step 1: Extract constraint satisfaction from NI Ligero + good challenges
  have h_sat_all : satisfiesAll w (generateAllConstraints p claimed_sum challenges) qcs :=
    niLigero_contrapositive w (generateAllConstraints p claimed_sum challenges) qcs
      niProof haccept h_lin_good h_quad_good
  -- Step 2: Split into sumcheck constraints + final constraint
  have ⟨h_sat, h_final⟩ :=
    satisfiesAllConstraints_split p claimed_sum challenges w h_sat_all.1
  -- Step 3: Constraint satisfaction → verifierAccepts on decoded rounds
  have hva :=
    witness_satisfies_implies_verifierAccepts p claimed_sum challenges w h_sat h_final
  -- Step 4: Decoded rounds have degree le 1
  have hdeg : ∀ i, (decodeRounds w challenges i).prover_poly.natDegree ≤ 1 :=
    fun i => polyFromEvals_natDegree _ _
  -- Step 5: sumcheck_soundness_det gives root hit
  obtain ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
    sumcheck_soundness_det p claimed_sum (decodeRounds w challenges) hn (by omega) hclaim hva hdeg
  -- Step 6: The challenge in decoded rounds IS challenges i
  simp only [decodeRounds] at hdiff_eval
  exact ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩

-- ============================================================
-- Section 2: Error bound for the probabilistic path
-- ============================================================

/-- **Probabilistic Longfellow error bound:** if the witness does not
    satisfy the generated constraints, then either the linear test bad
    set or the quadratic test bad set is small.

    This directly applies `niLigero_combined_error` to the Longfellow
    constraint system, giving a concrete bound on the probability that
    the NI Ligero verifier accepts despite constraint violation. -/
theorem probabilistic_longfellow_error_bound {n q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (w : Fin (witnessSize n) → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (hviol : ¬ satisfiesAll w (generateAllConstraints p claimed_sum challenges) qcs) :
    countSat (fun alpha : Fin (n + 1) → F =>
      linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges) alpha) ≤
        Fintype.card F ^ ((n + 1) - 1) ∨
    countSat (fun u : Fin q → F =>
      quadTestSingleChallenge w qcs u) ≤
        Fintype.card F ^ (q - 1) :=
  niLigero_combined_error w (generateAllConstraints p claimed_sum challenges) qcs hviol

-- ============================================================
-- Section 3: Full probabilistic E2E composition
-- ============================================================

omit [Field F] in
/-- **Full probabilistic composition:** composes the Longfellow error
    sources (sumcheck per layer, Ligero linear, Ligero quadratic, LDT)
    into a single error bound via `longfellow_total_error`.

    Given:
    - `NL` GKR layers, each with sumcheck error count at most `E_sc`
    - Ligero linear test error count at most `E_lin`
    - Ligero quadratic test error count at most `E_quad`
    - Ligero LDT error count at most `E_ldt`

    The total number of bad challenge vectors is at most
    `NL * E_sc + E_lin + E_quad + E_ldt`.

    This is the theorem that wires `longfellow_total_error` into the
    probabilistic Longfellow composition. -/
theorem probabilistic_longfellow_full_composition {n : ℕ}
    {NL : ℕ} {E_sc E_lin E_quad E_ldt : ℕ}
    -- Per-layer sumcheck bad event
    (P_sumcheck : Fin NL → RandomChallenges F n → Prop)
    [inst_sc : ∀ k, DecidablePred (P_sumcheck k)]
    -- Ligero test bad events
    (P_linear : RandomChallenges F n → Prop) [inst_lin : DecidablePred P_linear]
    (P_quad : RandomChallenges F n → Prop) [inst_quad : DecidablePred P_quad]
    (P_ldt : RandomChallenges F n → Prop) [inst_ldt : DecidablePred P_ldt]
    -- Overall bad event: verifier accepts despite wrong claim
    (P_bad : RandomChallenges F n → Prop) [inst_bad : DecidablePred P_bad]
    -- Individual bounds
    (sumcheck_bound : ∀ k : Fin NL, countSat (P_sumcheck k) ≤ E_sc)
    (linear_bound : countSat P_linear ≤ E_lin)
    (quad_bound : countSat P_quad ≤ E_quad)
    (ldt_bound : countSat P_ldt ≤ E_ldt)
    -- Decomposition: bad event implies one component fails
    (h_decomp : ∀ cs, P_bad cs →
      (∃ k, P_sumcheck k cs) ∨ P_linear cs ∨ P_quad cs ∨ P_ldt cs) :
    countSat P_bad ≤ NL * E_sc + E_lin + E_quad + E_ldt :=
  longfellow_total_error P_sumcheck P_linear P_quad P_ldt P_bad
    sumcheck_bound linear_bound quad_bound ldt_bound h_decomp

-- ============================================================
-- Section 4: Capstone — EndToEnd holds with good challenges
-- ============================================================

omit [Fintype F] in
/-- **Probabilistic Longfellow capstone:** the EndToEnd soundness
    conclusion holds whenever the NI Ligero verifier accepts with
    good challenges and the sumcheck challenges avoid polynomial roots.

    This connects the probabilistic path to the deterministic EndToEnd
    narrative: instead of requiring an abstract `LigeroScheme` with
    deterministic binding, we use `niLigeroVerify` with a probability
    bound on bad challenges.

    The probability that the combined bad event occurs is bounded by
    `longfellow_total_error`. When it does NOT occur, this theorem
    guarantees the full soundness conclusion. -/
theorem probabilistic_longfellow_capstone {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    -- NI Ligero accepted
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof)
    -- Good challenges for Ligero tests
    (h_lin_good : ¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) →
      ¬ linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges) niProof.alpha)
    (h_quad_good : ¬ (∀ i, satisfiesQuad w (qcs i)) →
      ¬ quadTestSingleChallenge w qcs niProof.u)
    -- No sumcheck challenge hits a polynomial root
    (hno_root : ∀ i : Fin n, ∀ diff : F[X],
      diff ≠ 0 → diff.natDegree ≤ 1 → diff.eval (challenges i) ≠ 0) :
    claimed_sum = ∑ b : Fin n → Bool, p.table b := by
  by_contra hclaim
  obtain ⟨i, diff, hne, hdeg, heval⟩ :=
    probabilistic_longfellow_soundness p claimed_sum hn hclaim w challenges qcs niProof
      haccept h_lin_good h_quad_good
  exact hno_root i diff hne hdeg heval

-- ============================================================
-- Section 5: Connecting error sources for concrete bounds
-- ============================================================

/-- **Concrete Longfellow error parameters:** instantiates the abstract
    `LongfellowErrorParams` with the concrete bounds from the codebase.

    For a Longfellow proof with:
    - `NL` GKR layers, each with `2*s` sumcheck rounds
    - Ligero with `m` linear constraints and `q` quadratic constraints
    - Field of size `|F|`

    The total error count is:
    - Per-layer sumcheck: `(2*s) * (2 * |F|^(2*s - 1))`
    - Ligero linear: `|F|^(m - 1)`
    - Ligero quadratic: `|F|^(q - 1)`
    - Ligero LDT: `E_ldt` (parameter, depends on RS distance) -/
noncomputable def concreteLongfellowError (NL s m q E_ldt : ℕ) : LongfellowErrorParams where
  num_layers := NL
  sumcheck_error_per_layer := (2 * s) * (2 * Fintype.card F ^ (2 * s - 1))
  ligero_linear_error := Fintype.card F ^ (m - 1)
  ligero_quad_error := Fintype.card F ^ (q - 1)
  ligero_ldt_error := E_ldt

omit [Field F] [DecidableEq F] in
/-- The total error count for the concrete Longfellow error parameters. -/
theorem concreteLongfellowError_total (NL s m q E_ldt : ℕ) :
    (concreteLongfellowError (F := F) NL s m q E_ldt).total =
      NL * ((2 * s) * (2 * Fintype.card F ^ (2 * s - 1))) +
      Fintype.card F ^ (m - 1) +
      Fintype.card F ^ (q - 1) +
      E_ldt := by
  unfold LongfellowErrorParams.total concreteLongfellowError
  ring

-- ============================================================
-- Section 6: Conditional probability statement
-- ============================================================

omit [DecidableEq F] [Fintype F] in
/-- **Conditional soundness:** if the NI Ligero verifier accepts,
    then either `satisfiesAll` holds (the witness is valid), or
    one of the Ligero test challenges is in a bad set whose size
    is bounded.

    This is a direct restatement of `niLigero_binding_or_bad` in
    the Longfellow context, making explicit that the probabilistic
    path feeds into the deterministic sumcheck chain. -/
theorem probabilistic_longfellow_conditional {n : ℕ}
    {params : LigeroParams} {q : ℕ}
    (p : MultilinearPoly F n)
    (claimed_sum : F)
    (challenges : Fin n → F)
    (w : Fin (witnessSize n) → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (niProof : NILigeroProof F params (n + 1) (witnessSize n) q)
    (haccept : niLigeroVerify w
      (generateAllConstraints p claimed_sum challenges) qcs niProof) :
    satisfiesAll w (generateAllConstraints p claimed_sum challenges) qcs ∨
    (¬ satisfiesLinear w (generateAllConstraints p claimed_sum challenges) ∧
     linearTestSingleChallenge w (generateAllConstraints p claimed_sum challenges) niProof.alpha) ∨
    (¬ (∀ i, satisfiesQuad w (qcs i)) ∧
     quadTestSingleChallenge w qcs niProof.u) :=
  niLigero_binding_or_bad w (generateAllConstraints p claimed_sum challenges) qcs niProof haccept

omit [Fintype F] in
/-- **Deterministic extraction from good challenges:** if
    `niLigeroVerify` accepts and we know `satisfiesAll` holds
    (e.g., because challenges are good), then the full deterministic
    Longfellow soundness chain applies.

    This shows that the deterministic `longfellow_soundness` theorem
    can be reached through the probabilistic path by first establishing
    constraint satisfaction. -/
theorem probabilistic_to_deterministic_bridge {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (h_sat_linear : satisfiesLinear w (generateConstraints claimed_sum challenges))
    (h_sat_final : satisfiesLinear w (generateFinalConstraint p challenges)) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 := by
  have hva :=
    witness_satisfies_implies_verifierAccepts p claimed_sum challenges w h_sat_linear h_sat_final
  have hdeg : ∀ i, (decodeRounds w challenges i).prover_poly.natDegree ≤ 1 :=
    fun i => polyFromEvals_natDegree _ _
  obtain ⟨i, diff, hne, hdeg_diff, heval⟩ :=
    sumcheck_soundness_det p claimed_sum (decodeRounds w challenges) hn (by omega) hclaim hva hdeg
  simp only [decodeRounds] at heval
  exact ⟨i, diff, hne, hdeg_diff, heval⟩
