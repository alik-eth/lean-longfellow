import LeanLongfellow.Sumcheck.Protocol

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F]

/-! # Sumcheck Completeness

If the claimed sum is correct and the prover is honest,
the verifier always accepts. The proof proceeds by induction on `n`,
using the clean recursive definition of `honestProver`.
-/

/-- **Sumcheck completeness:** if the claimed sum is correct and the prover is honest,
    the verifier always accepts. Error probability = 0. -/
theorem sumcheck_completeness {n : ℕ} (p : MultilinearPoly F n)
    (challenges : Fin n → F) :
    verifierAccepts p (∑ b : Fin n → Bool, p.table b) (honestProver p challenges) := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i, fun hn => absurd hn (by omega)⟩
  | succ m ih =>
    -- Reduced polynomial after fixing first variable
    have ih_inst := ih (p.partialEvalFirst (challenges 0)) (fun j => challenges j.succ)
    obtain ⟨ih_sum, ih_final⟩ := ih_inst
    refine ⟨fun i => ?_, fun hm => ?_⟩
    · -- Sum-check: for each round i
      refine Fin.cases ?_ (fun j => ?_) i
      · -- i = 0
        simp only [honestProver_zero]
        exact sumFirstVar_sum p
      · -- i = j.succ > 0
        simp only [honestProver_succ, show (j.succ : ℕ) ≠ 0 from Nat.succ_ne_zero _, ↓reduceIte]
        -- Previous round index: ⟨j.succ.val - 1, _⟩ = j.castSucc
        have hprev : (⟨(j.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = j.castSucc := by
          ext; simp [Fin.val_castSucc]
        rw [hprev]
        -- Use IH sum-check for j
        have ih_j := ih_sum j
        -- IH says: (hp reduced tail j).eval 0 + .eval 1 =
        --   if j.val = 0 then ∑ reduced.table else (hp reduced tail ⟨j-1,_⟩).eval (challenge)
        -- Our goal: same LHS = (hp p chall j.castSucc).prover_poly.eval (... .challenge)
        -- We need to show RHS_ours = RHS_ih
        rw [ih_j]
        split
        · -- j.val = 0
          rename_i hj0
          have : j.castSucc = (0 : Fin (m + 1)) := by ext; simp [Fin.val_castSucc, hj0]
          rw [this, honestProver_zero]
          show ∑ b, (p.partialEvalFirst (challenges 0)).table b =
            (sumFirstVar p).eval (challenges 0)
          exact partialEval_table_sum p (challenges 0)
        · -- j.val > 0
          rename_i hj_ne
          -- RHS of IH: (hp reduced tail ⟨j.val-1, _⟩).prover_poly.eval (... .challenge)
          -- Our RHS: (hp p chall j.castSucc).prover_poly.eval (... .challenge)
          -- j.castSucc.val = j.val, which > 0, so j.castSucc = ⟨j.val-1, _⟩.succ
          have hcast_succ : j.castSucc =
              (⟨j.val - 1, by omega⟩ : Fin m).succ := by
            ext; simp [Fin.val_castSucc]; omega
          rw [hcast_succ, honestProver_succ]
    · -- Final evaluation check
      -- Goal has `let last := ⟨m, _⟩`; show it explicitly
      show (honestProver p challenges ⟨m, by omega⟩).prover_poly.eval
             (honestProver p challenges ⟨m, by omega⟩).challenge =
           p.eval (fun i => (honestProver p challenges i).challenge)
      -- Express ⟨m, _⟩ as Fin.succ or 0
      cases m with
      | zero =>
        -- n = 1
        change (honestProver p challenges (0 : Fin 1)).prover_poly.eval
                 (honestProver p challenges (0 : Fin 1)).challenge =
               p.eval (fun i => (honestProver p challenges i).challenge)
        rw [honestProver_zero]
        simp only
        -- challenges for 1-var poly
        have : (fun i : Fin 1 => (honestProver p challenges i).challenge) =
            Fin.cons (challenges 0) Fin.elim0 := by
          funext i; fin_cases i; simp [Fin.cons_zero, honestProver_zero]
        rw [this]
        -- sumFirstVar(p).eval (challenges 0) = p.eval (Fin.cons (challenges 0) Fin.elim0)
        rw [show (sumFirstVar p).eval (challenges 0) =
            ∑ b : Fin 0 → Bool, (partialEvalFirst p (challenges 0)).table b from
          (partialEval_table_sum p (challenges 0)).symm]
        -- 0-var poly: ∑ table = eval at any point
        have h0eval : ∀ (q : MultilinearPoly F 0) (x : Fin 0 → F),
            ∑ b : Fin 0 → Bool, q.table b = q.eval x := by
          intro q x
          have hsub : ∀ (b : Fin 0 → Bool), b = Fin.elim0 :=
            fun b => funext (fun i => Fin.elim0 i)
          simp only [MultilinearPoly.eval, lagrangeBasis]
          rw [Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb),
              Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb)]
          simp [Finset.prod_empty]
        rw [h0eval, partialEvalFirst_eval]
      | succ m' =>
        -- n = m' + 2, ⟨m'+1, _⟩ = ⟨m', _⟩.succ
        have hsuc : (⟨m' + 1, by omega⟩ : Fin (m' + 2)) =
            (⟨m', by omega⟩ : Fin (m' + 1)).succ := by
          ext; simp
        rw [hsuc, honestProver_succ]
        -- IH final check: need to handle the `let` in ih_final
        have ih_fin := ih_final (by omega : 0 < m' + 1)
        -- ih_fin has form: let last := ⟨m', _⟩; ... = reduced.eval ...
        -- After simp only, the let should be inlined
        change _ at ih_fin
        -- The last index in ih_final: ⟨m'+1-1, _⟩ = ⟨m', _⟩
        trans (p.partialEvalFirst (challenges 0)).eval
            (fun i => (honestProver (p.partialEvalFirst (challenges 0))
              (fun k => challenges k.succ) i).challenge)
        · exact ih_fin
        · rw [partialEvalFirst_eval]
          congr 1
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [Fin.cons_zero, honestProver_zero]
          · simp [Fin.cons_succ, honestProver_succ]
