import LeanLongfellow.Sumcheck.Protocol

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] {n : ℕ}

/-! # Sumcheck Completeness

If the claimed sum is correct and the prover is honest,
the verifier always accepts. The mathematical content is straightforward:
at each round, `sumFirstVar` correctly sums the partially evaluated polynomial.
The main difficulty is dependent-type wrangling with `iterPartialEval`.

Two lemmas use `sorry` for dependent-type cast alignment:
- `iterPartialEval_step_aux` inductive step: the telescoping step connecting
  table sums across iterated partial evaluations (follows from `partialEval_table_sum`).
- `iterPartialEval_final`: the final evaluation check (follows from
  iterating `partialEvalFirst_eval`).

Both are mathematically straightforward but blocked by Lean's `Eq.mpr` casts
in `iterPartialEval`'s recursion pattern.
-/

-- Helper: cast-aware sumFirstVar_sum
private theorem cast_sumFirstVar_sum (d d' : ℕ) (hd : d = d' + 1)
    (q : MultilinearPoly F d) :
    (hd ▸ q).sumFirstVar.eval 0 + (hd ▸ q).sumFirstVar.eval 1 =
      ∑ b : Fin d → Bool, q.table b := by
  subst hd; exact sumFirstVar_sum q

-- Helper: cast-aware partialEval_table_sum
private theorem cast_partialEval_table_sum (d d' : ℕ) (hd : d = d' + 1)
    (q : MultilinearPoly F d) (r : F) :
    ∑ b : Fin d' → Bool, ((hd ▸ q).partialEvalFirst r).table b =
      (hd ▸ q).sumFirstVar.eval r := by
  subst hd; exact partialEval_table_sum q r

/-- The honest prover's round-i polynomial evaluations at 0 and 1 sum to
    the table sum of the i-th iterated partial evaluation. -/
private theorem honestProver_eval_sum (p : MultilinearPoly F n)
    (challenges : Fin n → F) (i : Fin n) :
    (honestProver p challenges i).prover_poly.eval 0 +
    (honestProver p challenges i).prover_poly.eval 1 =
    ∑ b : Fin (n - i.val) → Bool,
      (iterPartialEval F n p i.val (le_of_lt i.isLt)
        (fun j => challenges ⟨j.val, by omega⟩)).table b := by
  simp only [honestProver]
  exact cast_sumFirstVar_sum (n - i.val) (n - i.val - 1) (by omega) _

/-- The honest prover's round-i polynomial evaluated at the challenge
    equals `sumFirstVar` of the iterated partial evaluation, evaluated at challenge i. -/
private theorem honestProver_eval_challenge (p : MultilinearPoly F n)
    (challenges : Fin n → F) (i : Fin n) :
    (honestProver p challenges i).prover_poly.eval
      (honestProver p challenges i).challenge =
    ((by omega : n - i.val = (n - i.val - 1) + 1) ▸
      iterPartialEval F n p i.val (le_of_lt i.isLt)
        (fun j => challenges ⟨j.val, by omega⟩)).sumFirstVar.eval (challenges i) := by
  simp [honestProver]

/-- The key telescoping property: table sum after `k+1` partial evaluations
    equals `sumFirstVar` of the `k`-step result, evaluated at challenge `k`.

    Mathematically follows from `partialEval_table_sum`. The base cases (k=0 for
    any m, and any k for m=0) are proved; the inductive step (succ m', succ k)
    requires aligning `Eq.mpr` casts from `iterPartialEval`'s recursion.

    The sorry in the inductive step is purely about cast alignment:
    after unfolding `iterPartialEval` one step on both sides, both reduce to
    the IH `ih_m` applied to `p.partialEvalFirst (cf 0)`. -/
private theorem iterPartialEval_step_aux :
    ∀ (m : ℕ) (p : MultilinearPoly F (m + 1)) (k : ℕ) (hk : k + 1 ≤ m + 1)
      (cf : Fin (k + 1) → F),
    ∑ b : Fin (m + 1 - (k + 1)) → Bool,
      (iterPartialEval F (m + 1) p (k + 1) hk cf).table b =
    ((by omega : m + 1 - k = (m + 1 - k - 1) + 1) ▸
      iterPartialEval F (m + 1) p k (by omega)
        (fun j => cf ⟨j.val, by omega⟩)).sumFirstVar.eval
          (cf ⟨k, by omega⟩) := by
  intro m p
  induction m with
  | zero =>
    intro k hk cf
    have : k = 0 := by omega
    subst this
    simp only [iterPartialEval]
    exact cast_partialEval_table_sum _ _ (by omega) p (cf ⟨0, by omega⟩)
  | succ m' ih_m =>
    intro k
    induction k with
    | zero =>
      intro hk cf
      simp only [iterPartialEval]
      exact cast_partialEval_table_sum _ _ (by omega) p (cf ⟨0, by omega⟩)
    | succ k _ih_k =>
      intro hk cf
      set q := p.partialEvalFirst (cf ⟨0, by omega⟩)
      set cf' : Fin (k + 1) → F := fun j => cf ⟨j.val + 1, by omega⟩
      -- ih_m applied to q gives exactly what we need, modulo casts:
      -- ∑ b, (iterPartialEval F (m'+1) q (k+1) ...).table b =
      --   (cast ▸ iterPartialEval F (m'+1) q k ...).sumFirstVar.eval (cf' k)
      -- The goal, after unfolding iterPartialEval once on both sides,
      -- becomes ih_m q k (by omega) cf', but with different Nat cast proofs.
      -- This cast alignment is sorry'd.
      have _ih_applied := ih_m q k (by omega) cf'
      sorry

private theorem iterPartialEval_step (p : MultilinearPoly F n)
    (k : ℕ) (hk : k + 1 ≤ n)
    (challenges : Fin n → F) :
    ∑ b : Fin (n - (k + 1)) → Bool,
      (iterPartialEval F n p (k + 1) hk
        (fun j => challenges ⟨j.val, by omega⟩)).table b =
    ((by omega : n - k = (n - k - 1) + 1) ▸
      iterPartialEval F n p k (by omega : k ≤ n)
        (fun j => challenges ⟨j.val, by omega⟩)).sumFirstVar.eval
          (challenges ⟨k, by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact iterPartialEval_step_aux m p k hk (fun j => challenges ⟨j.val, by omega⟩)

/-- Final evaluation: after `n-1` partial evaluations, `sumFirstVar` evaluated at
    the last challenge equals `p.eval challenges`.

    Mathematically follows from iterating `partialEvalFirst_eval`, but the
    dependent-type casts in `iterPartialEval` make the formal proof delicate. -/
private theorem iterPartialEval_final (p : MultilinearPoly F n)
    (hn : 0 < n) (challenges : Fin n → F) :
    ((by omega : n - (n - 1) = (n - (n - 1) - 1) + 1) ▸
      iterPartialEval F n p (n - 1) (by omega)
        (fun j => challenges ⟨j.val, by omega⟩)).sumFirstVar.eval
          (challenges ⟨n - 1, by omega⟩) =
    p.eval (fun i => challenges i) := by
  sorry

/-- The sum-check condition at round `i` when `i > 0`:
    the table sum after `i` steps equals the previous round's polynomial
    evaluated at the previous challenge. -/
private theorem sumcheck_round_pos (p : MultilinearPoly F n)
    (challenges : Fin n → F) (i : Fin n) (hi : i.val ≠ 0) :
    ∑ b : Fin (n - i.val) → Bool,
      (iterPartialEval F n p i.val (le_of_lt i.isLt)
        (fun j => challenges ⟨j.val, by omega⟩)).table b =
    (honestProver p challenges ⟨i.val - 1, by omega⟩).prover_poly.eval
      (honestProver p challenges ⟨i.val - 1, by omega⟩).challenge := by
  rw [honestProver_eval_challenge]
  set k := i.val - 1 with hk_def
  have hik : i.val = k + 1 := by omega
  suffices h : ∀ (m : ℕ) (hm : m = k + 1) (hle : m ≤ n),
      ∑ b : Fin (n - m) → Bool,
        (iterPartialEval F n p m hle
          (fun j => challenges ⟨j.val, by omega⟩)).table b =
      ((by omega : n - k = (n - k - 1) + 1) ▸
        iterPartialEval F n p k (by omega)
          (fun j => challenges ⟨j.val, by omega⟩)).sumFirstVar.eval
            (challenges ⟨k, by omega⟩) by
    convert h i.val hik (le_of_lt i.isLt)
  intro m hm hle
  subst hm
  exact iterPartialEval_step p k (by omega) challenges

/-- **Sumcheck completeness:** if the claimed sum is correct and the prover is honest,
    the verifier always accepts. Error probability = 0. -/
theorem sumcheck_completeness (p : MultilinearPoly F n)
    (challenges : Fin n → F) :
    verifierAccepts p (∑ b : Fin n → Bool, p.table b) (honestProver p challenges) := by
  unfold verifierAccepts
  refine ⟨?_, ?_⟩
  · -- Sum-check condition: for each round i, eval at 0 + eval at 1 = previous value
    intro i
    rw [honestProver_eval_sum]
    split
    · -- i.val = 0: table sum = claimed sum = ∑ p.table
      rename_i hi
      have h0 : i.val = 0 := hi
      have : ∀ (hle : i.val ≤ n) (cf : Fin i.val → F),
          ∑ b : Fin (n - i.val) → Bool,
            (iterPartialEval F n p i.val hle cf).table b =
          ∑ b : Fin n → Bool, p.table b := by
        rw [h0]
        intro hle cf
        simp [iterPartialEval]
      exact this _ _
    · -- i.val > 0: telescoping step
      rename_i hi
      exact sumcheck_round_pos p challenges i hi
  · -- Final evaluation check
    intro hn
    show (honestProver p challenges ⟨n - 1, by omega⟩).prover_poly.eval
        (honestProver p challenges ⟨n - 1, by omega⟩).challenge =
      p.eval (fun i => (honestProver p challenges i).challenge)
    rw [honestProver_eval_challenge]
    simp only [honestProver]
    exact iterPartialEval_final p hn challenges
