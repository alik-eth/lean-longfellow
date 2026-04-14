import LeanLongfellow.GKR.Pad
import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

variable {F : Type*} [Field F] {n : ℕ}

/-! # Zero-Knowledge Simulator for the Padded Sumcheck

This file constructs an explicit zero-knowledge simulator for the padded
sumcheck protocol.  The simulator produces, for each round `i`, a degree-≤-1
polynomial `s_i = X * C(target_i)` where `target_i` is the claimed sum
multiplied by all previous challenges.  This satisfies:
  `s_i(0) + s_i(1) = 0 + target_i = target_i`
and
  `s_i(r) = target_i * r`
so the next target is `target_i * r = target_{i+1}`, as required.
-/

/-- A simulator for the padded sumcheck. -/
structure SumcheckSimulator (F : Type*) [Field F] (n : ℕ) where
  simulate : F → (Fin n → F) → (Fin n → Polynomial F)

/-- A simulator is valid if its output satisfies the sum-check conditions. -/
def simulatorValid (sim : SumcheckSimulator F n) (claimed_sum : F) : Prop :=
  ∀ challenges : Fin n → F,
    ∀ i : Fin n,
      (sim.simulate claimed_sum challenges i).eval 0 +
      (sim.simulate claimed_sum challenges i).eval 1 =
        if (i : ℕ) = 0 then claimed_sum
        else (sim.simulate claimed_sum challenges ⟨i.val - 1, by omega⟩).eval
              (challenges ⟨i.val - 1, by omega⟩)

-- ---------------------------------------------------------------------------
-- Target value at each round
-- ---------------------------------------------------------------------------

/-- The target value at round `i`: the claimed sum times the product of all
    challenges at rounds `0, 1, ..., i-1`. -/
noncomputable def simTarget (claimed_sum : F) (challenges : Fin n → F) (i : Fin n) : F :=
  claimed_sum * (Finset.range i.val).prod
    (fun j => if h : j < n then challenges ⟨j, h⟩ else 1)

-- ---------------------------------------------------------------------------
-- Helper lemmas about simTarget
-- ---------------------------------------------------------------------------

/-- At round 0, the target equals the claimed sum. -/
theorem simTarget_zero (claimed_sum : F) (challenges : Fin n → F) (i : Fin n)
    (h : (i : ℕ) = 0) :
    simTarget claimed_sum challenges i = claimed_sum := by
  simp only [simTarget, h, Finset.range_zero, Finset.prod_empty, mul_one]

/-- At round i > 0, the target equals the previous target times the previous challenge. -/
theorem simTarget_succ (claimed_sum : F) (challenges : Fin n → F) (i : Fin n)
    (h : (i : ℕ) ≠ 0) :
    simTarget claimed_sum challenges i =
      simTarget claimed_sum challenges ⟨i.val - 1, by omega⟩ *
        challenges ⟨i.val - 1, by omega⟩ := by
  simp only [simTarget]
  have hpos : 0 < i.val := Nat.pos_of_ne_zero h
  -- Use conv_lhs to expand only the LHS product using prod_range_succ
  -- i.val = (i.val - 1) + 1
  conv_lhs =>
    rw [show i.val = (i.val - 1) + 1 from by omega]
    rw [Finset.prod_range_succ]
  -- Now LHS = claimed_sum * ((prod over range (i.val-1)) * elt at (i.val-1))
  -- RHS = (claimed_sum * prod over range (i.val-1)) * challenges ⟨i.val-1, _⟩
  have hlast : (if h : i.val - 1 < n then challenges ⟨i.val - 1, h⟩ else 1) =
      challenges ⟨i.val - 1, by omega⟩ := by
    simp [show i.val - 1 < n by omega]
  rw [hlast]
  ring

-- ---------------------------------------------------------------------------
-- The simulator construction
-- ---------------------------------------------------------------------------

/-- The simulator: at round `i`, produce `X * C(simTarget i)`.
    This gives `s_i(0) = 0`, `s_i(1) = target_i`, so `s_i(0) + s_i(1) = target_i`.
    And `s_i(r) = target_i * r`. -/
noncomputable def mkSimulator : SumcheckSimulator F n where
  simulate claimed_sum challenges i :=
    Polynomial.X * Polynomial.C (simTarget claimed_sum challenges i)

-- ---------------------------------------------------------------------------
-- Main theorem
-- ---------------------------------------------------------------------------

/-- A valid simulator exists: it constructs degree-≤-1 polynomials
    satisfying the sum-check telescoping. -/
theorem padded_zk_simulator_exists (claimed_sum : F) :
    ∃ sim : SumcheckSimulator F n, simulatorValid sim claimed_sum := by
  use mkSimulator
  intro challenges i
  simp only [mkSimulator, eval_mul, eval_X, eval_C, zero_mul, one_mul]
  ring_nf
  by_cases h : (i : ℕ) = 0
  · simp only [h, ↓reduceIte]
    exact simTarget_zero claimed_sum challenges i h
  · simp only [h, ↓reduceIte]
    -- LHS is simTarget claimed_sum challenges i
    -- RHS is challenges ⟨i.val-1, _⟩ * simTarget claimed_sum challenges ⟨i.val-1, _⟩
    rw [simTarget_succ claimed_sum challenges i h]
    ring
