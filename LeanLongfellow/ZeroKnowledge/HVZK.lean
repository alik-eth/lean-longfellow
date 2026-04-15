import LeanLongfellow.ZeroKnowledge.Defs
import LeanLongfellow.Sumcheck.Pad

/-! # HVZK for Padded Sumcheck

The padded sumcheck protocol is honest-verifier zero-knowledge:
there exists a simulator that produces valid transcripts without
knowing the polynomial.

The simulator is built from `simulateRounds` (defined in `Sumcheck/Pad.lean`),
which constructs `simulatorPoly target = target * X` at each round --
a degree-le-1 polynomial whose values at 0 and 1 sum to `target`. -/

open Polynomial

variable {F : Type*} [Field F]

/-- Construct the HVZK simulator from the existing `simulateRounds`.
    For each round, the simulator sends `simulatorPoly target` where
    `target` is the claimed sum (round 0) or the previous round's
    polynomial evaluated at the previous challenge. -/
noncomputable def sumcheckHVZKSimulator (n : ℕ) : SumcheckSimulator F n where
  simulate claimed_sum challenges := simulateRounds claimed_sum challenges

/-- The sumcheck simulator is valid: its transcripts satisfy the
    sum-check telescoping conditions for any claimed sum and challenges. -/
theorem sumcheck_simulator_valid (n : ℕ) :
    simulatorValid (sumcheckHVZKSimulator n : SumcheckSimulator F n) := by
  intro claimed_sum challenges i
  exact simulateRounds_sum_check claimed_sum challenges i

/-- The sumcheck protocol is HVZK: there exists a simulator that
    produces valid transcripts without knowing the polynomial. -/
theorem sumcheck_isHVZK (n : ℕ) : isHVZK F n :=
  ⟨sumcheckHVZKSimulator n, sumcheck_simulator_valid n⟩
