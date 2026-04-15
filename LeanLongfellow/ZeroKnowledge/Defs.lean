import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Field.Defs

/-! # Zero-Knowledge Definitions

Formal definitions of honest-verifier zero-knowledge (HVZK) for
the sumcheck interactive proof system.

The key idea: a protocol is zero-knowledge if there exists a
*simulator* that produces transcripts satisfying the verifier's
checks WITHOUT access to the witness polynomial. -/

open Polynomial

variable {F : Type*} [Field F]

/-- A transcript of the sumcheck protocol: the prover's polynomials
    and verifier's challenges for each round. -/
def SumcheckTranscript (F : Type*) [Field F] (n : ℕ) :=
  Fin n → SumcheckRound F

/-- The sum-check telescoping conditions only (no final evaluation check).
    Round 0: poly(0) + poly(1) = claimed_sum
    Round i > 0: poly(0) + poly(1) = prev_poly(prev_challenge)

    This is what a simulator can satisfy without knowing the polynomial p.
    The full `verifierAccepts` also checks that the last round's polynomial
    evaluates correctly against `p`, which requires knowledge of `p`. -/
def sumCheckConditions {n : ℕ} (claimed_sum : F)
    (transcript : SumcheckTranscript F n) : Prop :=
  ∀ i : Fin n,
    (transcript i).prover_poly.eval 0 + (transcript i).prover_poly.eval 1 =
      if (i : ℕ) = 0 then claimed_sum
      else (transcript ⟨i.val - 1, by omega⟩).prover_poly.eval
            (transcript ⟨i.val - 1, by omega⟩).challenge

/-- A simulator for the sumcheck protocol: given the claimed sum and
    verifier challenges, produces a transcript WITHOUT access to the
    polynomial p. -/
structure SumcheckSimulator (F : Type*) [Field F] (n : ℕ) where
  simulate : F → (Fin n → F) → SumcheckTranscript F n

/-- A simulator is VALID if its output passes the verifier's sum-check
    conditions for any challenges and any claimed sum. This is the
    functional characterization of HVZK: the simulated transcript is
    accepted by the verifier (modulo the final evaluation check). -/
def simulatorValid {n : ℕ} (sim : SumcheckSimulator F n) : Prop :=
  ∀ (claimed_sum : F) (challenges : Fin n → F),
    sumCheckConditions claimed_sum (sim.simulate claimed_sum challenges)

/-- The sumcheck protocol is HVZK if there exists a valid simulator. -/
def isHVZK (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∃ sim : SumcheckSimulator F n, simulatorValid sim

/-- Stronger: perfect HVZK -- the simulated transcript has the SAME
    distribution as the real transcript. For deterministic simulators
    this means: for any challenges, the simulated round polynomials
    are the unique degree-le-1 polynomials that pass the verifier. -/
def isPerfectHVZK (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∃ sim : SumcheckSimulator F n,
    simulatorValid sim ∧
    -- Uniqueness: any valid degree-le-1 transcript must equal the simulated one
    ∀ (claimed_sum : F) (challenges : Fin n → F)
      (transcript : SumcheckTranscript F n),
        -- transcript uses the same challenges
        (∀ i, (transcript i).challenge = challenges i) →
        -- transcript passes sum-check conditions
        sumCheckConditions claimed_sum transcript →
        -- all round polynomials have degree le 1
        (∀ i, (transcript i).prover_poly.natDegree ≤ 1) →
        -- then the polynomials must match the simulator's
        ∀ i, (transcript i).prover_poly = (sim.simulate claimed_sum challenges i).prover_poly
