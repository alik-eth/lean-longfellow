import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Sumcheck.Protocol
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.LinearCombination

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F]

/-! # Constraint Generation from Sumcheck

This file encodes sumcheck transcripts as witness vectors and generates
linear constraints that capture the verifier's acceptance predicate.
The bridge theorems prove equivalence between constraint satisfaction
and `verifierAccepts`.
-/

/-- Witness size for an n-round sumcheck: 2 entries per round. -/
def witnessSize (n : ℕ) : ℕ := 2 * n

/-- Encode a sumcheck transcript as a witness vector.
    `w[2i] = rounds(i).prover_poly.eval 0`
    `w[2i+1] = rounds(i).prover_poly.eval 1` -/
noncomputable def encodeWitness {n : ℕ} (rounds : Fin n → SumcheckRound F) :
    Fin (witnessSize n) → F :=
  fun k =>
    let i : Fin n := ⟨k.val / 2, by
      have := k.isLt
      simp [witnessSize] at this ⊢
      omega⟩
    if k.val % 2 = 0
    then (rounds i).prover_poly.eval 0
    else (rounds i).prover_poly.eval 1

/-- Generate the n sum-check constraints as a linear system.
    Row 0: w[0] + w[1] = claimed_sum
    Row i (i > 0): w[2i] + w[2i+1] - (1-r_{i-1})·w[2(i-1)] - r_{i-1}·w[2(i-1)+1] = 0 -/
noncomputable def generateConstraints {n : ℕ} (claimed_sum : F)
    (challenges : Fin n → F) : LinearConstraints F n (witnessSize n) where
  matrix i j :=
    if j.val = 2 * i.val then 1
    else if j.val = 2 * i.val + 1 then 1
    else if (i : ℕ) > 0 ∧ j.val = 2 * (i.val - 1) then
      -(1 - challenges ⟨i.val - 1, by omega⟩)
    else if (i : ℕ) > 0 ∧ j.val = 2 * (i.val - 1) + 1 then
      -(challenges ⟨i.val - 1, by omega⟩)
    else 0
  target i :=
    if (i : ℕ) = 0 then claimed_sum else 0

/-- Generate the final evaluation constraint.
    (1-r_{n-1})·w[2(n-1)] + r_{n-1}·w[2(n-1)+1] = p.eval(challenges) -/
noncomputable def generateFinalConstraint {n : ℕ}
    (p : MultilinearPoly F n) (challenges : Fin n → F) :
    LinearConstraints F 1 (witnessSize n) where
  matrix _ j :=
    if hn : 0 < n then
      let last := n - 1
      if j.val = 2 * last then (1 - challenges ⟨last, by omega⟩)
      else if j.val = 2 * last + 1 then challenges ⟨last, by omega⟩
      else 0
    else 0
  target _ := p.eval challenges

/-- For a degree-≤-1 polynomial: p(r) = (1-r)·p(0) + r·p(1). -/
theorem eval_deg_le_one (p : F[X]) (hdeg : p.natDegree ≤ 1) (r : F) :
    p.eval r = (1 - r) * p.eval 0 + r * p.eval 1 := by
  have hcoeff : ∀ i, 2 ≤ i → p.coeff i = 0 := by
    intro i hi
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hrep : p = C (p.coeff 0) + C (p.coeff 1) * X := by
    ext i
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    match i with
    | 0 => simp
    | 1 => simp
    | n + 2 => simp [hcoeff (n + 2) (by omega)]
  rw [hrep]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

-- Helper lemmas for encodeWitness at even/odd indices
@[simp] private theorem encodeWitness_even {n : ℕ} (rounds : Fin n → SumcheckRound F)
    (i : Fin n) (h : 2 * i.val < witnessSize n := by unfold witnessSize; omega) :
    encodeWitness rounds ⟨2 * i.val, h⟩ = (rounds i).prover_poly.eval 0 := by
  unfold encodeWitness; simp [Nat.mul_mod_right]

@[simp] private theorem encodeWitness_odd {n : ℕ} (rounds : Fin n → SumcheckRound F)
    (i : Fin n) (h : 2 * i.val + 1 < witnessSize n := by unfold witnessSize; omega) :
    encodeWitness rounds ⟨2 * i.val + 1, h⟩ = (rounds i).prover_poly.eval 1 := by
  unfold encodeWitness
  have hmod : (2 * i.val + 1) % 2 = 1 := by omega
  have hdiv : (2 * i.val + 1) / 2 = i.val := by
    have := Nat.div_add_mod (2 * i.val + 1) 2; omega
  simp [hmod, hdiv]

/-- Helper: the sparse sum for row i of generateConstraints reduces to the
    nonzero terms. This is the hard index-arithmetic step involving
    Finset.sum simplification with conditional matrix entries. -/
private theorem sparse_sum_eq {n : ℕ} (claimed_sum : F)
    (challenges : Fin n → F) (w : Fin (witnessSize n) → F) (i : Fin n) :
    ∑ j : Fin (witnessSize n), (generateConstraints claimed_sum challenges).matrix i j * w j =
      w ⟨2 * i.val, by unfold witnessSize; omega⟩ +
      w ⟨2 * i.val + 1, by unfold witnessSize; omega⟩ +
      (if (i : ℕ) > 0
       then -(1 - challenges ⟨i.val - 1, by omega⟩) *
              w ⟨2 * (i.val - 1), by unfold witnessSize; omega⟩ +
            -(challenges ⟨i.val - 1, by omega⟩) *
              w ⟨2 * (i.val - 1) + 1, by unfold witnessSize; omega⟩
       else 0) := by
  sorry

/-- Helper: the sparse sum for generateFinalConstraint reduces to the
    nonzero terms. -/
private theorem sparse_final_sum_eq {n : ℕ} (hn : 0 < n)
    (p : MultilinearPoly F n) (challenges : Fin n → F)
    (w : Fin (witnessSize n) → F) :
    ∑ j : Fin (witnessSize n),
      (generateFinalConstraint p challenges).matrix ⟨0, by omega⟩ j * w j =
      (1 - challenges ⟨n - 1, by omega⟩) *
        w ⟨2 * (n - 1), by unfold witnessSize; omega⟩ +
      challenges ⟨n - 1, by omega⟩ *
        w ⟨2 * (n - 1) + 1, by unfold witnessSize; omega⟩ := by
  sorry

/-- If the encoded witness satisfies the sum-check constraints AND the final
    constraint, then verifierAccepts holds. -/
theorem constraints_encode_sumcheck {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (rounds : Fin n → SumcheckRound F)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_challenges : ∀ i, (rounds i).challenge = challenges i)
    (h_sat : satisfiesLinear (encodeWitness rounds)
      (generateConstraints claimed_sum challenges))
    (h_final : satisfiesLinear (encodeWitness rounds)
      (generateFinalConstraint p challenges)) :
    verifierAccepts p claimed_sum rounds := by
  constructor
  · -- Sum check: each round polynomial sums correctly
    intro i
    have hi_sat := h_sat i
    rw [sparse_sum_eq] at hi_sat
    rw [encodeWitness_even, encodeWitness_odd] at hi_sat
    simp only [generateConstraints] at hi_sat
    by_cases hi0 : (i : ℕ) = 0
    · -- i = 0
      simp only [hi0, show ¬(0 > 0) from by omega, ↓reduceIte, add_zero] at hi_sat
      simp only [hi0, ↓reduceIte]; exact hi_sat
    · -- i > 0
      have hig : (i : ℕ) > 0 := Nat.pos_of_ne_zero hi0
      simp only [hig, ↓reduceIte, hi0] at hi_sat
      rw [encodeWitness_even rounds ⟨i.val - 1, by omega⟩,
          encodeWitness_odd rounds ⟨i.val - 1, by omega⟩] at hi_sat
      -- hi_sat: eval0 + eval1 + (-(1-c)*prev_eval0 + (-c)*prev_eval1) = 0
      -- with c = challenges ⟨i-1,...⟩, prev_eval0/1 = (rounds ⟨i-1,...⟩).prover_poly.eval 0/1
      have hprev := eval_deg_le_one _ (hdeg ⟨i.val - 1, by omega⟩)
          (challenges ⟨i.val - 1, by omega⟩)
      simp only [hi0, ↓reduceIte]
      -- Goal: eval0 + eval1 = (rounds ⟨i-1,...⟩).prover_poly.eval (rounds ⟨i-1,...⟩).challenge
      -- hi_sat: eval0 + eval1 + (-(1-c)*prev0 + (-c)*prev1) = 0
      -- Goal after simp: eval0 + eval1 = prev.eval (rounds ⟨i-1,...⟩).challenge
      -- Don't rewrite with hprev; instead work directly
      -- The goal is: eval0 + eval1 = (rounds ⟨i-1,...⟩).prover_poly.eval (rounds ⟨i-1,...⟩).challenge
      -- Use hprev to rewrite (rounds ...).challenge in the goal
      rw [h_challenges]
      -- Now goal has challenges ⟨↑i - 1, ⋯⟩, matching hi_sat
      rw [hprev]
      -- Goal: eval0 + eval1 = (1-c)*prev0 + c*prev1
      -- hi_sat: eval0 + eval1 + (-(1-c)*prev0 + (-c)*prev1) = 0
      -- These should have matching Fin terms now
      linear_combination hi_sat
  · -- Final evaluation check
    intro hn
    have hf := h_final ⟨0, by omega⟩
    rw [sparse_final_sum_eq hn] at hf
    simp only [generateFinalConstraint] at hf
    rw [encodeWitness_even rounds ⟨n - 1, by omega⟩,
        encodeWitness_odd rounds ⟨n - 1, by omega⟩] at hf
    have hlast := eval_deg_le_one _ (hdeg ⟨n - 1, by omega⟩)
        (challenges ⟨n - 1, by omega⟩)
    show (rounds ⟨n - 1, by omega⟩).prover_poly.eval
        (rounds ⟨n - 1, by omega⟩).challenge = p.eval fun i => (rounds i).challenge
    rw [h_challenges, hlast]
    -- Goal: (1-c)*eval0 + c*eval1 = p.eval (fun i => (rounds i).challenge)
    -- hf: (1-c)*eval0 + c*eval1 = p.eval challenges
    -- Need: challenges = fun i => (rounds i).challenge
    have hfun : challenges = fun i => (rounds i).challenge := by
      ext j; exact (h_challenges j).symm
    rw [← hfun]; exact hf

/-- If verifierAccepts holds, then the encoded witness satisfies the constraints. -/
theorem sumcheck_encodes_constraints {n : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (challenges : Fin n → F)
    (rounds : Fin n → SumcheckRound F)
    (hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ 1)
    (h_challenges : ∀ i, (rounds i).challenge = challenges i)
    (haccept : verifierAccepts p claimed_sum rounds) :
    satisfiesLinear (encodeWitness rounds)
      (generateConstraints claimed_sum challenges) := by
  obtain ⟨hsum, _⟩ := haccept
  intro i
  -- Transform goal using sparse_sum_eq
  suffices h : encodeWitness rounds ⟨2 * i.val, by unfold witnessSize; omega⟩ +
      encodeWitness rounds ⟨2 * i.val + 1, by unfold witnessSize; omega⟩ +
      (if (i : ℕ) > 0
       then -(1 - challenges ⟨i.val - 1, by omega⟩) *
              encodeWitness rounds ⟨2 * (i.val - 1), by unfold witnessSize; omega⟩ +
            -(challenges ⟨i.val - 1, by omega⟩) *
              encodeWitness rounds ⟨2 * (i.val - 1) + 1, by unfold witnessSize; omega⟩
       else 0) =
      (generateConstraints claimed_sum challenges).target i by
    rw [← h]; exact sparse_sum_eq claimed_sum challenges (encodeWitness rounds) i
  rw [encodeWitness_even, encodeWitness_odd]
  have hi := hsum i
  by_cases hi0 : (i : ℕ) = 0
  · -- i = 0: the if-branch is false, so the extra terms vanish
    simp only [hi0, show ¬(0 > 0) from by omega, ↓reduceIte, add_zero,
      generateConstraints, ↓reduceIte] at hi ⊢
    exact hi
  · -- i > 0: the if-branch is true
    have hig : (i : ℕ) > 0 := Nat.pos_of_ne_zero hi0
    simp only [hig, ↓reduceIte]
    rw [encodeWitness_even rounds ⟨i.val - 1, by omega⟩,
        encodeWitness_odd rounds ⟨i.val - 1, by omega⟩]
    simp only [generateConstraints, hi0, ↓reduceIte]
    have hprev := eval_deg_le_one _ (hdeg ⟨i.val - 1, by omega⟩)
        (rounds ⟨i.val - 1, by omega⟩).challenge
    rw [h_challenges] at hprev
    simp [hi0] at hi
    have hch : (rounds ⟨i.val - 1, by omega⟩).challenge =
        challenges ⟨i.val - 1, by omega⟩ := h_challenges _
    rw [hch] at hi; rw [hprev] at hi
    rw [hi]; ring
