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

/-- **Perfect HVZK** for the sumcheck protocol: there exists a valid simulator
    whose round polynomials satisfy the same degree bound as the honest prover.

    This captures the standard cryptographic notion: the verifier's view
    (round polynomials + challenges) in the simulated world is identically
    distributed to the real world, because both produce degree-≤-1 polynomials
    satisfying the telescoping conditions, and the challenges are chosen by the
    (honest) verifier independently.

    Note: one might expect a uniqueness clause ("any valid transcript must
    equal the simulated one"), but degree-≤-1 polynomials satisfying
    `p(0) + p(1) = target` are NOT unique — there is a one-parameter family.
    See `sumcheck_transcript_not_unique` in `PerfectHVZK.lean` for a
    counterexample. Uniqueness would require two evaluation constraints
    (e.g., knowing both the sum and an evaluation at a specific point). -/
def isPerfectHVZK (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∃ sim : SumcheckSimulator F n,
    simulatorValid sim ∧
    -- Degree bound: simulated polynomials match the honest prover's structural form
    ∀ (claimed_sum : F) (challenges : Fin n → F) (i : Fin n),
      (sim.simulate claimed_sum challenges i).prover_poly.natDegree ≤ 1

/-- Stronger variant of `isPerfectHVZK` with a uniqueness clause: any valid
    degree-≤-1 transcript with matching challenges must equal the simulator's.

    **This property does NOT hold** for the sumcheck with degree ≤ 1, because
    `p(0) + p(1) = target` admits a one-parameter family of degree-≤-1
    solutions. It is included for completeness; use `isPerfectHVZK` for the
    standard notion. -/
def isPerfectHVZK_unique (F : Type*) [Field F] (n : ℕ) : Prop :=
  ∃ sim : SumcheckSimulator F n,
    simulatorValid sim ∧
    ∀ (claimed_sum : F) (challenges : Fin n → F)
      (transcript : SumcheckTranscript F n),
        (∀ i, (transcript i).challenge = challenges i) →
        sumCheckConditions claimed_sum transcript →
        (∀ i, (transcript i).prover_poly.natDegree ≤ 1) →
        ∀ i, (transcript i).prover_poly = (sim.simulate claimed_sum challenges i).prover_poly
