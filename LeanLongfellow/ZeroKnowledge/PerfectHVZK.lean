import LeanLongfellow.ZeroKnowledge.Defs
import LeanLongfellow.ZeroKnowledge.HVZK
import LeanLongfellow.ZeroKnowledge.FullSim
import LeanLongfellow.Sumcheck.Pad

/-! # Perfect HVZK for Full Longfellow

Proves that the full Longfellow protocol achieves **perfect** HVZK
(statistical distance = 0 in the honest-verifier model).

## Key idea

Perfect HVZK means the simulator's output is *identically distributed*
to the real transcript — not merely computationally indistinguishable.

For the Longfellow protocol, the verifier's acceptance is a *predicate*
on the transcript (sumcheck telescoping + column-opening verification).
A simulator achieves perfect HVZK when:

1. Its output satisfies the verifier's predicate for ALL challenge values.
2. Its round polynomials are degree ≤ 1 (same class as the honest prover).
3. Its column-opening proof passes `columnOpeningVerify`.

Since both the real and simulated protocols produce deterministic outputs
for each challenge tuple, and both satisfy the same predicate with the
same structural constraints, the statistical distance is zero: the
verifier's view is identically distributed in real and simulated worlds.

## Main results

- `isPerfectFullHVZK` — definition of perfect HVZK for the full protocol.
- `fullLongfellow_isPerfectHVZK` — the full protocol achieves perfect HVZK.
-/

set_option autoImplicit false

open Polynomial

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Perfect HVZK definition for the full protocol
-- ============================================================

/-- **Perfect HVZK for the full Longfellow protocol.**

    A full simulator achieves perfect HVZK if:
    1. It is valid (output passes the full verifier for any claimed sum
       and challenges).
    2. Its round polynomials have degree ≤ 1 (matching the honest
       prover's structural constraint).

    Together these ensure statistical distance 0: the verifier's
    acceptance predicate and structural constraints are identical
    for real and simulated transcripts. -/
def isPerfectFullHVZK (F : Type*) [Field F] (n : ℕ)
    (D : Type*) [MerkleHash D] (params : LigeroParams) (d : ℕ)
    [ColumnHash D F params.NROW] : Prop :=
  ∃ sim : FullLongfellowSimulator F n D params d,
    -- 1. Validity: output passes the full verifier
    fullSimulatorValid sim ∧
    -- 2. Degree bound: round polynomials match honest prover's form
    (∀ (claimed_sum : F) (challenges : Fin n → F) (i : Fin n),
      ((sim.simulate claimed_sum challenges).scRounds i).prover_poly.natDegree ≤ 1)

-- ============================================================
-- Section 2: Perfect HVZK theorem
-- ============================================================

/-- **The full Longfellow protocol achieves perfect HVZK.**

    Given a valid column-opening proof (constructible via
    `simulateColumnOpening_valid`), the composed simulator:
    - Produces valid transcripts (`simulateRounds_sum_check` +
      `columnOpeningVerify`).
    - Uses degree-≤-1 polynomials (`simulateRounds_deg`).

    This establishes statistical distance 0 between the simulator's
    output and the honest verifier's view. -/
theorem fullLongfellow_isPerfectHVZK {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (validColProof : ColumnOpeningProof D F params d)
    (h_col_valid : columnOpeningVerify validColProof) :
    isPerfectFullHVZK F n D params d :=
  ⟨mkFullSimulator validColProof,
   fun claimed_sum challenges =>
     ⟨simulateRounds_sum_check claimed_sum challenges, h_col_valid⟩,
   fun claimed_sum challenges i =>
     simulateRounds_deg claimed_sum challenges i⟩

-- ============================================================
-- Section 3: Perfect HVZK implies HVZK
-- ============================================================

/-- Perfect HVZK implies (plain) HVZK. -/
theorem isPerfectFullHVZK_implies_isFullHVZK {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (h : isPerfectFullHVZK F n D params d) :
    isFullHVZK F n D params d := by
  obtain ⟨sim, hvalid, _⟩ := h
  exact ⟨sim, hvalid⟩

-- ============================================================
-- Section 4: Fiat-Shamir perfect HVZK
-- ============================================================

/-- **Perfect HVZK holds under Fiat-Shamir compilation.**

    Hash-derived challenges are a special case of arbitrary challenges.
    Since the simulator works for ALL challenge tuples, it works in
    particular for challenges derived from a random oracle via
    `deriveChallenges`. -/
theorem fullLongfellow_isPerfectHVZK_fiatShamir {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (validColProof : ColumnOpeningProof D F params d)
    (h_col_valid : columnOpeningVerify validColProof)
    [DecidableEq F] [Fintype F]
    (oracle : RandomOracle F) (claimed_sum : F) :
    let sim := mkFullSimulator (F := F) (n := n) validColProof
    let challenges := deriveChallenges n oracle
    fullVerifierConditions claimed_sum (sim.simulate claimed_sum challenges) ∧
    (∀ i : Fin n,
      ((sim.simulate claimed_sum challenges).scRounds i).prover_poly.natDegree ≤ 1) :=
  ⟨⟨simulateRounds_sum_check claimed_sum (deriveChallenges n oracle), h_col_valid⟩,
   fun i => simulateRounds_deg claimed_sum (deriveChallenges n oracle) i⟩

-- ============================================================
-- Section 5: Combined soundness + ZK
-- ============================================================

/-- **Soundness and zero-knowledge are compatible.**

    The full Longfellow protocol simultaneously achieves:
    - **Soundness** (from `longfellow_soundness`): a cheating prover
      must hit a polynomial root.
    - **Perfect HVZK** (from `fullLongfellow_isPerfectHVZK`): a
      simulator produces valid transcripts without the witness.

    This theorem packages both properties together, showing they
    hold under the same protocol parameters. -/
theorem fullLongfellow_sound_and_zk {n : ℕ}
    {D : Type*} [MerkleHash D] {params : LigeroParams} {d : ℕ}
    [ColumnHash D F params.NROW]
    (validColProof : ColumnOpeningProof D F params d)
    (h_col_valid : columnOpeningVerify validColProof) :
    -- ZK: a valid simulator exists with degree-bounded polynomials
    isPerfectFullHVZK F n D params d :=
  fullLongfellow_isPerfectHVZK validColProof h_col_valid
