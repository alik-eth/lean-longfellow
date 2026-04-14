# Degree-d Sumcheck Generalization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize sumcheck soundness and Fiat-Shamir bounds from degree ≤ 1 to degree ≤ d, enabling degree-2 Longfellow round polynomials.

**Architecture:** Parameterize soundness theorems by implicit `{d : ℕ}`. Degree bound moves from hardcoded `≤ 1` to hypothesis `≤ d`. Rewrite `countSat_adaptive_root` with fiber-counting proof to support d > 1 roots. `verifierAccepts`, `SumcheckRound`, and witness encoding are unchanged.

**Tech Stack:** Lean 4 (v4.30.0-rc1), Mathlib4 (`Polynomial.card_roots'`, `Finset.card_eq_sum_card_fiberwise`, `Fin.insertNthEquiv`)

**Spec:** `docs/specs/2026-04-14-degree-d-sumcheck-generalization-design.md`

---

### Task 1: Generalize Sumcheck Soundness to Degree ≤ d

**Files:**
- Modify: `LeanLongfellow/Sumcheck/Soundness.lean`
- Modify: `LeanLongfellow/Ligero/Longfellow.lean` (fix call site)

This task deletes the custom `roots_le_one_of_deg_le_one` lemma, generalizes both soundness theorems from degree ≤ 1 to degree ≤ d, and fixes the downstream call site in Longfellow.lean.

- [ ] **Step 1: Delete `roots_le_one_of_deg_le_one` and generalize `sumcheck_soundness_det`**

In `LeanLongfellow/Sumcheck/Soundness.lean`, delete lines 23-37 (`roots_le_one_of_deg_le_one` — it's only used in Oracle.lean's `countSat_root_hit`, not here, and we'll replace that usage in Task 2).

Then replace `sumcheck_soundness_det` (lines 49-177) with the degree-d version. The changes are:
1. Add `{d : ℕ}` implicit and `(hd : 1 ≤ d)` explicit parameter
2. Change `hdeg` from `≤ 1` to `≤ d`
3. Change conclusion from `diff.natDegree ≤ 1` to `diff.natDegree ≤ d`
4. In the proof, change `hdiff₀_deg` to use `le_trans (sumFirstVar_natDegree_le p) hd`
5. Pass `hd` to the recursive `ih` call

Replace the full theorem with:

```lean
/-- **Sumcheck deterministic soundness (degree ≤ d).**

If the verifier accepts a claimed sum that differs from the true sum,
then there exists a round `i` and a nonzero polynomial `diff` of degree ≤ d
whose evaluation at the challenge `rounds i` is zero.

The `1 ≤ d` hypothesis is needed because the honest prover polynomial has
degree ≤ 1, so `diff = adversary - honest` has degree ≤ max(d, 1) = d. -/
theorem sumcheck_soundness_det {n : ℕ} {d : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hn : 0 < n)
    (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds)
    (hdeg : ∀ i : Fin n, (rounds i).prover_poly.natDegree ≤ d) :
    ∃ i : Fin n, ∃ (diff : F[X]), diff ≠ 0 ∧ diff.natDegree ≤ d ∧
      diff.eval (rounds i).challenge = 0 := by
  revert p claimed_sum rounds hn hclaim haccept hdeg
  induction n with
  | zero => intro _ _ _ hn; omega
  | succ m ih =>
    intro p claimed_sum rounds _hn hclaim haccept hdeg
    obtain ⟨haccept_sum, haccept_final⟩ := haccept
    -- Round 0 polynomials
    set g₀ := (rounds 0).prover_poly with hg₀_def
    set h₀ := p.sumFirstVar with hh₀_def
    set r₀ := (rounds 0).challenge with hr₀_def
    -- g₀(0) + g₀(1) = claimed_sum
    have hg₀_sum : g₀.eval 0 + g₀.eval 1 = claimed_sum := by
      have := haccept_sum (0 : Fin (m + 1)); simp at this; exact this
    -- h₀(0) + h₀(1) = ∑ p.table
    have hh₀_sum : h₀.eval 0 + h₀.eval 1 = ∑ b, p.table b := sumFirstVar_sum p
    -- g₀ ≠ h₀
    have hg₀_ne_h₀ : g₀ ≠ h₀ := by
      intro heq; exact hclaim (hg₀_sum.symm.trans (by rw [heq]; exact hh₀_sum))
    -- Difference polynomial
    set diff₀ := g₀ - h₀
    have hdiff₀_ne : diff₀ ≠ 0 := sub_ne_zero.mpr hg₀_ne_h₀
    have hdiff₀_deg : diff₀.natDegree ≤ d := by
      calc diff₀.natDegree ≤ max g₀.natDegree h₀.natDegree := natDegree_sub_le g₀ h₀
      _ ≤ d := Nat.max_le.mpr ⟨hdeg 0, le_trans (sumFirstVar_natDegree_le p) hd⟩
    by_cases hdiff₀_eval : diff₀.eval r₀ = 0
    · exact ⟨0, diff₀, hdiff₀_ne, hdiff₀_deg, hdiff₀_eval⟩
    · -- g₀(r₀) ≠ h₀(r₀), so the propagated claim is wrong
      have heval_ne : g₀.eval r₀ ≠ h₀.eval r₀ := by
        intro heq; exact hdiff₀_eval (by simp [diff₀, Polynomial.eval_sub, heq])
      set reduced := p.partialEvalFirst r₀
      have hclaim' : g₀.eval r₀ ≠ ∑ b, reduced.table b := by
        rwa [← show h₀.eval r₀ = ∑ b, reduced.table b from
          (partialEval_table_sum p r₀).symm]
      -- Build verifierAccepts for the reduced protocol
      set rounds' : Fin m → SumcheckRound F := fun j => rounds j.succ
      have hdeg' : ∀ i : Fin m, (rounds' i).prover_poly.natDegree ≤ d := fun i => hdeg i.succ
      -- Simplify haccept_final
      have hfinal : (rounds ⟨m, by omega⟩).prover_poly.eval
            (rounds ⟨m, by omega⟩).challenge =
          p.eval (fun i => (rounds i).challenge) :=
        haccept_final (by omega)
      -- Build the sum-check condition for the reduced protocol
      have haccept'_sum : ∀ i : Fin m,
          (rounds' i).prover_poly.eval 0 + (rounds' i).prover_poly.eval 1 =
            if (i : ℕ) = 0 then g₀.eval r₀
            else (rounds' ⟨i.val - 1, by omega⟩).prover_poly.eval
                  (rounds' ⟨i.val - 1, by omega⟩).challenge := by
        intro i
        have horig := haccept_sum i.succ
        simp only [show (i.succ : ℕ) ≠ 0 from Nat.succ_ne_zero _, ↓reduceIte] at horig
        have hfin : (⟨(i.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = ⟨i.val, by omega⟩ := by
          ext; simp
        rw [hfin] at horig
        split
        · rename_i hi0
          have : (⟨i.val, by omega⟩ : Fin (m + 1)) = 0 := by ext; exact hi0
          rw [this] at horig
          exact horig
        · rename_i hi_ne
          have : (⟨i.val - 1, by omega⟩ : Fin m).succ = (⟨i.val, by omega⟩ : Fin (m + 1)) := by
            ext; simp; omega
          simp only [rounds'] at horig ⊢
          rw [this]
          exact horig
      -- Build the final evaluation check for the reduced protocol
      have haccept'_final : ∀ (hm : 0 < m),
          let last : Fin m := ⟨m - 1, by omega⟩
          (rounds' last).prover_poly.eval (rounds' last).challenge =
            reduced.eval (fun i => (rounds' i).challenge) := by
        intro hm
        simp only
        have hlast : (⟨m - 1, by omega⟩ : Fin m).succ = (⟨m, by omega⟩ : Fin (m + 1)) := by
          ext; simp; omega
        simp only [rounds'] at hfinal ⊢
        rw [hlast, hfinal, partialEvalFirst_eval]
        congr 1; funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.cons_zero, hr₀_def]
        · simp [Fin.cons_succ]
      have haccept' : verifierAccepts reduced (g₀.eval r₀) rounds' :=
        ⟨haccept'_sum, haccept'_final⟩
      -- Apply IH or handle base case
      cases m with
      | zero =>
        exfalso; apply hclaim'
        have h0sum : ∀ (q : MultilinearPoly F 0) (x : Fin 0 → F),
            ∑ b : Fin 0 → Bool, q.table b = q.eval x := by
          intro q x
          have hsub : ∀ (b : Fin 0 → Bool), b = Fin.elim0 :=
            fun b => funext (fun i => Fin.elim0 i)
          simp only [MultilinearPoly.eval, lagrangeBasis]
          rw [Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb),
              Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb)]
          simp [Finset.prod_empty]
        rw [h0sum reduced Fin.elim0, partialEvalFirst_eval]
        simp only [g₀, r₀] at hfinal ⊢
        convert hfinal using 1
      | succ m' =>
        obtain ⟨j, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
          ih reduced (g₀.eval r₀) rounds' (by omega) hclaim' haccept' hdeg'
        exact ⟨j.succ, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩
```

- [ ] **Step 2: Generalize `sumcheck_soundness_concrete`**

Replace `sumcheck_soundness_concrete` (lines 179-295 after deletion of `roots_le_one_of_deg_le_one`) with the degree-d version. Key changes:
1. Add `{d : ℕ}` implicit parameter (NO `hd` needed — conclusion doesn't mention degree)
2. Change `hdeg` from `≤ 1` to `≤ d`
3. Delete the unused `hdiff₀_deg` computation (lines 210-213 in original)
4. The rest of the proof is unchanged — it never references degree values

```lean
/-- **Concrete sumcheck soundness (degree ≤ d).**

Like `sumcheck_soundness_det`, but the witness diff is pinned to
`rounds(i).prover_poly - (honestProver p challenges i).prover_poly`
where `challenges k = (rounds k).challenge`. -/
theorem sumcheck_soundness_concrete {n : ℕ} {d : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds)
    (hdeg : ∀ i : Fin n, (rounds i).prover_poly.natDegree ≤ d) :
    let challenges := fun k => (rounds k).challenge
    ∃ i : Fin n,
      (rounds i).prover_poly ≠ (honestProver p challenges i).prover_poly ∧
      ((rounds i).prover_poly - (honestProver p challenges i).prover_poly).eval
        (rounds i).challenge = 0 := by
  simp only
  revert p claimed_sum rounds hn hclaim haccept hdeg
  induction n with
  | zero => intro _ _ _ hn; omega
  | succ m ih =>
    intro p claimed_sum rounds _hn hclaim haccept hdeg
    obtain ⟨haccept_sum, haccept_final⟩ := haccept
    set g₀ := (rounds 0).prover_poly with hg₀_def
    set h₀ := p.sumFirstVar with hh₀_def
    set r₀ := (rounds 0).challenge with hr₀_def
    have hg₀_sum : g₀.eval 0 + g₀.eval 1 = claimed_sum := by
      have := haccept_sum (0 : Fin (m + 1)); simp at this; exact this
    have hh₀_sum : h₀.eval 0 + h₀.eval 1 = ∑ b, p.table b := sumFirstVar_sum p
    have hg₀_ne_h₀ : g₀ ≠ h₀ := by
      intro heq; exact hclaim (hg₀_sum.symm.trans (by rw [heq]; exact hh₀_sum))
    set diff₀ := g₀ - h₀
    have hdiff₀_ne : diff₀ ≠ 0 := sub_ne_zero.mpr hg₀_ne_h₀
    by_cases hdiff₀_eval : diff₀.eval r₀ = 0
    · -- Round 0 is the witness
      refine ⟨0, ?_, ?_⟩
      · simp only [honestProver_zero]; exact hg₀_ne_h₀
      · simp only [honestProver_zero]
        show (g₀ - h₀).eval r₀ = 0
        exact hdiff₀_eval
    · -- Propagate to next round (same as sumcheck_soundness_det)
      have heval_ne : g₀.eval r₀ ≠ h₀.eval r₀ := by
        intro heq; exact hdiff₀_eval (by simp [diff₀, Polynomial.eval_sub, heq])
      set reduced := p.partialEvalFirst r₀
      have hclaim' : g₀.eval r₀ ≠ ∑ b, reduced.table b := by
        rwa [← show h₀.eval r₀ = ∑ b, reduced.table b from
          (partialEval_table_sum p r₀).symm]
      set rounds' : Fin m → SumcheckRound F := fun j => rounds j.succ
      have hdeg' : ∀ i : Fin m, (rounds' i).prover_poly.natDegree ≤ d := fun i => hdeg i.succ
      -- Build verifierAccepts for the reduced protocol (same as before)
      have hfinal : (rounds ⟨m, by omega⟩).prover_poly.eval
            (rounds ⟨m, by omega⟩).challenge =
          p.eval (fun i => (rounds i).challenge) :=
        haccept_final (by omega)
      have haccept'_sum : ∀ i : Fin m,
          (rounds' i).prover_poly.eval 0 + (rounds' i).prover_poly.eval 1 =
            if (i : ℕ) = 0 then g₀.eval r₀
            else (rounds' ⟨i.val - 1, by omega⟩).prover_poly.eval
                  (rounds' ⟨i.val - 1, by omega⟩).challenge := by
        intro i
        have horig := haccept_sum i.succ
        simp only [show (i.succ : ℕ) ≠ 0 from Nat.succ_ne_zero _, ↓reduceIte] at horig
        have hfin : (⟨(i.succ : ℕ) - 1, by omega⟩ : Fin (m + 1)) = ⟨i.val, by omega⟩ := by
          ext; simp
        rw [hfin] at horig
        split
        · rename_i hi0
          have : (⟨i.val, by omega⟩ : Fin (m + 1)) = 0 := by ext; exact hi0
          rw [this] at horig; exact horig
        · rename_i hi_ne
          have : (⟨i.val - 1, by omega⟩ : Fin m).succ = (⟨i.val, by omega⟩ : Fin (m + 1)) := by
            ext; simp; omega
          simp only [rounds'] at horig ⊢; rw [this]; exact horig
      have haccept'_final : ∀ (hm : 0 < m),
          let last : Fin m := ⟨m - 1, by omega⟩
          (rounds' last).prover_poly.eval (rounds' last).challenge =
            reduced.eval (fun i => (rounds' i).challenge) := by
        intro hm; simp only
        have hlast : (⟨m - 1, by omega⟩ : Fin m).succ = (⟨m, by omega⟩ : Fin (m + 1)) := by
          ext; simp; omega
        simp only [rounds'] at hfinal ⊢
        rw [hlast, hfinal, partialEvalFirst_eval]
        congr 1; funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Fin.cons_zero, hr₀_def]
        · simp [Fin.cons_succ]
      have haccept' : verifierAccepts reduced (g₀.eval r₀) rounds' :=
        ⟨haccept'_sum, haccept'_final⟩
      cases m with
      | zero =>
        exfalso; apply hclaim'
        have h0sum : ∀ (q : MultilinearPoly F 0) (x : Fin 0 → F),
            ∑ b : Fin 0 → Bool, q.table b = q.eval x := by
          intro q x
          have hsub : ∀ (b : Fin 0 → Bool), b = Fin.elim0 :=
            fun b => funext (fun i => Fin.elim0 i)
          simp only [MultilinearPoly.eval, lagrangeBasis]
          rw [Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb),
              Fintype.sum_eq_single Fin.elim0 (fun b hb => absurd (hsub b) hb)]
          simp [Finset.prod_empty]
        rw [h0sum reduced Fin.elim0, partialEvalFirst_eval]
        simp only [g₀, r₀] at hfinal ⊢
        convert hfinal using 1
      | succ m' =>
        -- IH gives us j for the reduced protocol
        have challenges'_eq : (fun k => (rounds' k).challenge) = fun k => (rounds k.succ).challenge := rfl
        obtain ⟨j, hj_ne, hj_eval⟩ :=
          ih reduced (g₀.eval r₀) rounds' (by omega) hclaim' haccept' hdeg'
        refine ⟨j.succ, ?_, ?_⟩
        · simp only [honestProver_succ]
          exact hj_ne
        · simp only [honestProver_succ]
          exact hj_eval
```

- [ ] **Step 3: Fix call site in Longfellow.lean**

In `LeanLongfellow/Ligero/Longfellow.lean`, line 163-164, the call to `sumcheck_soundness_det` needs the new `hd` argument. Since `hdeg` provides degree ≤ 1 (from `polyFromEvals_natDegree`), `d` is inferred as 1 and `hd : 1 ≤ 1` is solved by `by omega`.

Change line 163-164 from:
```lean
  obtain ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
    sumcheck_soundness_det p claimed_sum (decodeRounds w challenges) hn hclaim hva hdeg
```
to:
```lean
  obtain ⟨i, diff, hdiff_ne, hdiff_deg, hdiff_eval⟩ :=
    sumcheck_soundness_det p claimed_sum (decodeRounds w challenges) hn (by omega) hclaim hva hdeg
```

- [ ] **Step 4: Build and verify**

Run: `lake build`
Expected: Compiles successfully with no new errors. The 2 existing sorry's in `Generate.lean` remain unchanged.

- [ ] **Step 5: Commit**

```bash
git add LeanLongfellow/Sumcheck/Soundness.lean LeanLongfellow/Ligero/Longfellow.lean
git commit -m "feat(Sumcheck): generalize soundness from degree ≤ 1 to degree ≤ d"
```

---

### Task 2: Generalize Oracle Counting to Degree ≤ d

**Files:**
- Modify: `LeanLongfellow/FiatShamir/Oracle.lean`

This task generalizes `countSat_root_hit` and rewrites `countSat_adaptive_root` with a fiber-counting proof that supports d > 1 roots per fiber.

- [ ] **Step 1: Generalize `countSat_root_hit`**

In `LeanLongfellow/FiatShamir/Oracle.lean`, replace `countSat_root_hit` (lines 174-205) with the degree-d version. The bound changes from `|F|^(n-1)` to `d * |F|^(n-1)`.

Key proof change: `hroots` becomes `d.roots.toFinset.card ≤ d` (via `Multiset.toFinset_card_le`, `card_roots'`, and `hdeg`). Final calc uses `≤ d * |F|^(n-1)` instead of `≤ 1 * |F|^(n-1)`.

```lean
/-- A nonzero polynomial of degree ≤ d vanishes on at most `d * |F|^(n-1)` challenge
    vectors at any given coordinate. -/
theorem countSat_root_hit {n : ℕ} {d : ℕ} (i : Fin n)
    {p : Polynomial F} (hp : p ≠ 0) (hdeg : p.natDegree ≤ d) :
    countSat (fun cs : RandomChallenges F n => p.eval (cs i) = 0) ≤
      d * Fintype.card F ^ (n - 1) := by
  have hroots : p.roots.toFinset.card ≤ d := by
    calc p.roots.toFinset.card
        ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := card_roots' p
      _ ≤ d := hdeg
  have hsub : univ.filter (fun cs : RandomChallenges F n => p.eval (cs i) = 0) ⊆
      p.roots.toFinset.biUnion
        (fun r => univ.filter (fun cs : RandomChallenges F n => cs i = r)) := by
    intro cs hcs
    rw [mem_filter] at hcs
    rw [mem_biUnion]
    have hroot : p.IsRoot (cs i) := IsRoot.def.mpr hcs.2
    exact ⟨cs i, Multiset.mem_toFinset.mpr ((mem_roots hp).mpr hroot),
           mem_filter.mpr ⟨mem_univ cs, rfl⟩⟩
  calc (univ.filter (fun cs => p.eval (cs i) = 0)).card
      ≤ (p.roots.toFinset.biUnion
          (fun r => univ.filter (fun cs : RandomChallenges F n => cs i = r))).card :=
        card_le_card hsub
    _ ≤ ∑ r ∈ p.roots.toFinset,
          (univ.filter (fun cs : RandomChallenges F n => cs i = r)).card :=
        card_biUnion_le
    _ = ∑ _r ∈ p.roots.toFinset, Fintype.card F ^ (n - 1) := by
        congr 1; ext r; exact countSat_eq_val i r
    _ = p.roots.toFinset.card * Fintype.card F ^ (n - 1) := by
        simp [Finset.sum_const]
    _ ≤ d * Fintype.card F ^ (n - 1) :=
        Nat.mul_le_mul_right _ hroots
```

- [ ] **Step 2: Rewrite `countSat_adaptive_root` with fiber counting**

Replace `countSat_adaptive_root` (lines 112-170) with the degree-d version. This is the hardest change — the current injectivity proof breaks for d > 1 because a degree-d polynomial can have up to d roots.

**New proof strategy (fiber counting):**
1. Partition the satisfying set by the `n-1` non-`i` coordinates (the "fiber" of each `g : Fin m → F`)
2. On each fiber, `D` is constant (by `hD_indep`) — call it `D_g`
3. If `D_g = 0`: the `D cs ≠ 0` condition fails, so 0 elements in this fiber
4. If `D_g ≠ 0`: at most `d` values of `cs i` satisfy `D_g.eval v = 0` (by `card_roots'` + `hD_deg`)
5. Summing over `|F|^(n-1)` fibers: total ≤ `d * |F|^(n-1)`

```lean
/-- If `D(cs)` depends on all coordinates except `i`, has degree ≤ d, and we count
    the `cs` where `D(cs) ≠ 0` and `D(cs).eval(cs i) = 0`, the count is ≤ `d * |F|^(n-1)`.

    Proof: partition by the `n-1` coordinates other than `i`. For each fiber,
    `D` is constant (by `hD_indep`). If `D = 0` the `≠ 0` condition fails;
    if `D ≠ 0` at most `d` values of `cs i` are roots. So each fiber contributes
    at most `d`, and there are `|F|^(n-1)` fibers. -/
theorem countSat_adaptive_root {n : ℕ} {d : ℕ} (i : Fin n)
    (D : RandomChallenges F n → Polynomial F)
    (hD_indep : ∀ cs cs', (∀ j, j ≠ i → cs j = cs' j) → D cs = D cs')
    (hD_deg : ∀ cs, (D cs).natDegree ≤ d) :
    countSat (fun cs => D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) ≤
      d * Fintype.card F ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  simp only [Nat.add_sub_cancel]
  unfold countSat
  set S := univ.filter (fun cs : Fin (m + 1) → F => D cs ≠ 0 ∧ (D cs).eval (cs i) = 0)
  -- Project to the (n-1) non-i coordinates
  let proj : (Fin (m + 1) → F) → (Fin m → F) := fun cs j => cs (i.succAbove j)
  -- D is constant on fibers of proj
  have hD_const : ∀ cs₁ cs₂ : Fin (m + 1) → F, proj cs₁ = proj cs₂ → D cs₁ = D cs₂ := by
    intro cs₁ cs₂ hproj
    apply hD_indep
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    exact congr_fun hproj k
  -- Decompose by fiber: S.card = ∑_g (S ∩ fiber_g).card
  have hdecomp : S.card = ∑ g ∈ (univ : Finset (Fin m → F)),
      (S.filter (fun cs => proj cs = g)).card :=
    Finset.card_eq_sum_card_fiberwise (fun cs hcs => mem_univ (proj cs))
  rw [hdecomp]
  -- Bound each fiber by d
  calc ∑ g ∈ univ, (S.filter (fun cs => proj cs = g)).card
      ≤ ∑ _g ∈ (univ : Finset (Fin m → F)), d := by
        apply Finset.sum_le_sum
        intro g _hg
        -- In fiber g: every cs has proj cs = g, so cs = Fin.insertNth i v g for some v
        -- D is constant on this fiber: D cs = D (Fin.insertNth i 0 g) for all cs in fiber
        set D_g := D (Fin.insertNth i 0 g)
        -- The fiber elements satisfying the predicate are {v : F | D_g ≠ 0 ∧ D_g.eval v = 0}
        -- If D_g = 0: no elements satisfy D cs ≠ 0, so count = 0 ≤ d
        -- If D_g ≠ 0: the satisfying v's are roots of D_g, at most d by card_roots'
        by_cases hDg : D_g = 0
        · -- D_g = 0: no elements can satisfy D cs ≠ 0
          have : S.filter (fun cs => proj cs = g) = ∅ := by
            rw [Finset.eq_empty_iff_forall_not_mem]
            intro cs hcs
            rw [Finset.mem_filter] at hcs
            have hcs_S := hcs.1
            rw [Finset.mem_filter] at hcs_S
            have hne := hcs_S.2.1
            have hproj := hcs.2
            have : D cs = D_g := hD_const cs (Fin.insertNth i 0 g) (by
              funext j; simp [proj] at hproj; rw [hproj]; simp [Fin.insertNth_apply_succAbove])
            rw [this, hDg] at hne
            exact hne rfl
          rw [this, Finset.card_empty]; omega
        · -- D_g ≠ 0: at most d roots
          -- Map fiber elements to F via cs ↦ cs i
          -- The image is contained in roots of D_g
          have hle : (S.filter (fun cs => proj cs = g)).card ≤
              (univ.filter (fun v : F => D_g.eval v = 0)).card := by
            apply Finset.card_le_card_of_injOn (fun cs => cs i)
              (fun cs hcs => by
                rw [Finset.mem_filter] at hcs ⊢
                have hcs_S := hcs.1
                rw [Finset.mem_filter] at hcs_S
                refine ⟨mem_univ _, ?_⟩
                have hproj := hcs.2
                have hDeq : D cs = D_g := hD_const cs (Fin.insertNth i 0 g) (by
                  funext j; simp [proj] at hproj; rw [hproj]
                  simp [Fin.insertNth_apply_succAbove])
                rw [← hDeq]; exact hcs_S.2.2)
              (fun cs₁ hcs₁ cs₂ hcs₂ heqi => by
                rw [Finset.mem_coe, Finset.mem_filter] at hcs₁ hcs₂
                have hproj₁ := hcs₁.2
                have hproj₂ := hcs₂.2
                funext j
                by_cases hj : j = i
                · subst hj; exact heqi
                · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
                  simp [proj] at hproj₁ hproj₂
                  exact (congr_fun hproj₁ k).symm.trans (congr_fun hproj₂ k))
          calc (S.filter (fun cs => proj cs = g)).card
              ≤ (univ.filter (fun v : F => D_g.eval v = 0)).card := hle
            _ ≤ D_g.roots.toFinset.card := by
                apply Finset.card_le_card
                intro v hv
                rw [Finset.mem_filter] at hv
                exact Multiset.mem_toFinset.mpr ((mem_roots hDg).mpr (IsRoot.def.mpr hv.2))
            _ ≤ D_g.roots.card := Multiset.toFinset_card_le _
            _ ≤ D_g.natDegree := card_roots' _
            _ ≤ d := hD_deg _
    _ = Fintype.card F ^ m * d := by
        simp [Finset.sum_const, Finset.card_univ, card_randomChallenges]
    _ = d * Fintype.card F ^ m := by ring
```

**Important note for the implementer:** The proof above captures the correct strategy but may need tactical adjustments for Lean to accept. The key difficulties are:
- The `proj cs = g` filter needs careful handling of `Fin.insertNth` and `Fin.succAbove`
- The injectivity argument for `cs ↦ cs i` within a fiber requires showing `proj cs₁ = proj cs₂ = g` implies `cs₁` and `cs₂` agree on all non-`i` coordinates
- `hD_deg _` at the end needs the right `cs` argument — use `Fin.insertNth i 0 g`

If the proof has issues, the `hD_const` lemma and the fiber-by-fiber bound are the load-bearing steps. Debug by checking each `calc` step independently.

- [ ] **Step 3: Build and verify**

Run: `lake build`
Expected: Compiles successfully. Note: `FiatShamir/Soundness.lean` will likely NOT build yet because it references the old `countSat_adaptive_root` signature. That's expected — Task 3 fixes it.

Verify that `Oracle.lean` itself compiles:
Run: `lake build LeanLongfellow.FiatShamir.Oracle`
Expected: Success.

- [ ] **Step 4: Commit**

```bash
git add LeanLongfellow/FiatShamir/Oracle.lean
git commit -m "feat(FiatShamir): generalize countSat_adaptive_root and countSat_root_hit to degree ≤ d"
```

---

### Task 3: Generalize Fiat-Shamir Soundness to Degree ≤ d

**Files:**
- Modify: `LeanLongfellow/FiatShamir/Soundness.lean`

This task generalizes `fiatShamir_soundness` to use the degree-d versions of `sumcheck_soundness_concrete` and `countSat_adaptive_root`.

- [ ] **Step 1: Generalize `fiatShamir_soundness`**

In `LeanLongfellow/FiatShamir/Soundness.lean`, replace `fiatShamir_soundness` (lines 72-146) with the degree-d version. Key changes:
1. Add `{d : ℕ}` implicit and `(hd : 1 ≤ d)` explicit parameter
2. Change `hdeg` from `≤ 1` to `≤ d`
3. Change bound from `n * Fintype.card F ^ (n - 1)` to `n * (d * Fintype.card F ^ (n - 1))`
4. `countSat_adaptive_root` now returns `≤ d * |F|^(n-1)` with `hD_deg` providing `≤ d`
5. The degree bound on the diff: `max(adversary_deg, honest_deg) ≤ max(d, 1) = d` (using `hd`)

```lean
/-- **Fiat-Shamir ROM Soundness (degree ≤ d).**
For any non-adaptive adversary sending degree-≤-d polynomials, if the claimed sum
is wrong, the number of challenge vectors that fool the verifier is at most
`n * d * |F|^(n-1)`. Dividing by |F|^n gives probability bound `n·d / |F|`.

For Longfellow with degree-2 combining polynomial, instantiate d = 2 to get
bound `2n / |F|`. -/
theorem fiatShamir_soundness {n : ℕ} {d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1)) := by
  -- Per-round bad event using the CONCRETE diff between adversary and honest polys.
  let D : Fin n → RandomChallenges F n → Polynomial F := fun i cs =>
    (adversary cs).round_polys i - (honestProver p cs i).prover_poly
  let Q : Fin n → RandomChallenges F n → Prop := fun i cs =>
    D i cs ≠ 0 ∧ (D i cs).eval (cs i) = 0
  -- Step 1: Show the bad set is contained in the union of per-round bad events
  suffices h_sub : ∀ cs, fsVerifierAccepts p claimed_sum (adversary cs) cs → ∃ i, Q i cs by
    -- Step 2: Apply union bound
    calc countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs)
        ≤ countSat (fun cs => ∃ i : Fin n, Q i cs) :=
          countSat_mono h_sub
      _ ≤ n * (d * Fintype.card F ^ (n - 1)) := by
          have h_bound : ∀ j : Fin n, countSat (Q j) ≤ d * Fintype.card F ^ (n - 1) := by
            intro i
            apply countSat_adaptive_root i (D i)
            · -- Independence: D i cs depends only on cs j for j < i, hence not on cs i
              intro cs cs' hagree
              simp only [D]
              congr 1
              · apply h_nonadaptive cs cs' i
                intro j hj
                exact hagree j (by omega)
              · exact honestProver_poly_indep p i cs cs'
                  (fun j hj => hagree j (by omega))
            · -- Degree bound
              intro cs
              simp only [D]
              calc ((adversary cs).round_polys i - (honestProver p cs i).prover_poly).natDegree
                  ≤ max ((adversary cs).round_polys i).natDegree
                        ((honestProver p cs i).prover_poly).natDegree :=
                    Polynomial.natDegree_sub_le _ _
                _ ≤ d := Nat.max_le.mpr ⟨hdeg cs i,
                    le_trans (honestProver_deg_le p cs i) hd⟩
          exact countSat_union_bound Q h_bound
  -- Step 1 proof: use sumcheck_soundness_concrete to get the concrete diff
  intro cs hfs
  have haccept : verifierAccepts p claimed_sum (toRounds (adversary cs) cs) := hfs
  have hdeg_rounds : ∀ i : Fin n, (toRounds (adversary cs) cs i).prover_poly.natDegree ≤ d :=
    fun i => by simp only [toRounds]; exact hdeg cs i
  obtain ⟨i, hi_ne, hi_eval⟩ :=
    sumcheck_soundness_concrete p claimed_sum (toRounds (adversary cs) cs) hn hclaim haccept hdeg_rounds
  have hchal : (fun k => (toRounds (adversary cs) cs k).challenge) = cs := by
    funext k; simp [toRounds]
  rw [hchal] at hi_ne
  simp only [toRounds] at hi_ne
  refine ⟨i, ?_, ?_⟩
  · simp only [D]
    exact sub_ne_zero.mpr hi_ne
  · simp only [D]
    exact hi_eval
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: Full project compiles successfully. All 3 modified files plus all unchanged files build. The 2 existing sorry's in `Generate.lean` remain the only sorry's.

- [ ] **Step 3: Commit**

```bash
git add LeanLongfellow/FiatShamir/Soundness.lean
git commit -m "feat(FiatShamir): generalize ROM soundness bound to n·d/|F| for degree ≤ d"
```

---

### Task 4: Full Build Verification and Cleanup

**Files:**
- None modified (verification only)

- [ ] **Step 1: Full clean build**

Run: `lake clean && lake build`
Expected: Compiles successfully with no errors.

- [ ] **Step 2: Verify sorry count**

Run: `grep -r "sorry" LeanLongfellow/ --include="*.lean" -l`
Expected: Only `LeanLongfellow/Ligero/Generate.lean` (the 2 pre-existing sorry's in `sparse_sum_eq` and `sparse_final_sum_eq`).

- [ ] **Step 3: Verify backward compatibility**

Check that the degree-1 case still works by confirming these files build without changes:
- `Sumcheck/Completeness.lean` — uses `honestProver_deg_le` (degree ≤ 1), unmodified
- `Ligero/Longfellow.lean` — uses `sumcheck_soundness_det` with `d = 1`, fixed in Task 1
- `Ligero/Generate.lean` — uses `eval_deg_le_one` (degree ≤ 1), unmodified

Run: `lake build`
Expected: All pass.
