import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Polynomial.Roots

/-! # Random Oracle Model — Probability Counting Infrastructure

This file provides a minimal probability counting infrastructure for Random Oracle
Model soundness proofs. Instead of modelling the oracle as a function
`Polynomial F → F` (which ranges over an infinite domain), we model it as
`RandomChallenges F n = Fin n → F` — one uniformly random field element per round.
This is equivalent for non-adaptive adversaries.

## Main definitions
- `RandomChallenges F n`: type of challenge vectors (= `Fin n → F`).
- `countSat P`: number of challenge vectors satisfying predicate `P`.

## Main results
- `card_randomChallenges`: `|RandomChallenges F n| = |F|^n`.
- `countSat_eq_val`: the fiber `{cs | cs i = v}` has size `|F|^(n-1)`.
- `countSat_union_bound`: union bound over `m` events each of size ≤ `k`.
- `countSat_root_hit`: a nonzero degree-≤-d polynomial vanishes on at most
  `d * |F|^(n-1)` challenge vectors at any given coordinate.
-/

open Finset Polynomial

/-- Random challenges: one uniformly random field element per round. -/
abbrev RandomChallenges (F : Type*) (n : ℕ) := Fin n → F

/-- Count how many challenge assignments satisfy a predicate. -/
noncomputable def countSat {F : Type*} [DecidableEq F] [Fintype F]
    {n : ℕ} (P : RandomChallenges F n → Prop) [DecidablePred P] : ℕ :=
  (Finset.univ.filter P).card

/-- The total number of challenge assignments is |F|^n. -/
theorem card_randomChallenges (F : Type*) [Fintype F] (n : ℕ) :
    Fintype.card (RandomChallenges F n) = Fintype.card F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fintype.card_congr (Fin.insertNthEquiv (fun _ : Fin (n + 1) => F) 0).symm,
        Fintype.card_prod, ih, pow_succ, mul_comm]

/-- The fiber `{cs | cs i = v}` has cardinality `|F|^(n-1)`. -/
theorem countSat_eq_val {F : Type*} [DecidableEq F] [Fintype F]
    {n : ℕ} (i : Fin n) (v : F) :
    countSat (fun cs : RandomChallenges F n => cs i = v) = Fintype.card F ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  simp only [Nat.add_sub_cancel]
  unfold countSat
  rw [show (univ.filter (fun cs : Fin (m + 1) → F => cs i = v)).card =
      Fintype.card (Fin m → F) from ?_,
      card_randomChallenges]
  -- Show filter card = Fintype.card (Fin m → F) via a bijection that drops coordinate i
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨cs, _⟩ => fun j => cs (i.succAbove j)
    invFun := fun g => ⟨Fin.insertNth i v g, by simp [Fin.insertNth_apply_same]⟩
    left_inv := by
      rintro ⟨cs, hcs⟩
      simp only [Subtype.mk.injEq]
      funext j
      by_cases hji : j = i
      · subst hji; rw [Fin.insertNth_apply_same]; exact hcs.symm
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        rw [Fin.insertNth_apply_succAbove]
    right_inv := by
      intro g
      funext j
      simp only
      rw [Fin.insertNth_apply_succAbove]
  }

/-- **Union bound**: if each of `m` events has at most `k` satisfying assignments,
    then their union has at most `m * k` satisfying assignments. -/
theorem countSat_union_bound {F : Type*} [DecidableEq F] [Fintype F]
    {n m : ℕ} {k : ℕ}
    (P : Fin m → RandomChallenges F n → Prop)
    [∀ j, DecidablePred (P j)]
    (hbound : ∀ j, countSat (P j) ≤ k) :
    countSat (fun cs => ∃ j, P j cs) ≤ m * k := by
  unfold countSat
  have hsub : univ.filter (fun cs => ∃ j, P j cs) ⊆
      Finset.univ.biUnion (fun j => univ.filter (P j)) := by
    intro cs hcs
    rw [mem_filter] at hcs
    rw [mem_biUnion]
    obtain ⟨j, hj⟩ := hcs.2
    exact ⟨j, mem_univ j, mem_filter.mpr ⟨mem_univ cs, hj⟩⟩
  calc (univ.filter (fun cs => ∃ j, P j cs)).card
      ≤ (Finset.univ.biUnion (fun j => univ.filter (P j))).card :=
        card_le_card hsub
    _ ≤ ∑ j : Fin m, (univ.filter (P j)).card :=
        card_biUnion_le
    _ ≤ ∑ _ : Fin m, k :=
        Finset.sum_le_sum (fun j _ => hbound j)
    _ = m * k := by simp [Finset.sum_const]

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- If `D(cs)` depends on all coordinates except `i`, has degree ≤ d, and we count
    the `cs` where `D(cs) ≠ 0` and `D(cs).eval(cs i) = 0`, the count is ≤ `d * |F|^(n-1)`.

    Proof (fiber counting): partition the satisfying set by the `n-1` coordinates
    other than `i` via `proj cs = (fun j => cs (i.succAbove j))`. On each fiber,
    `D` is constant (by `hD_indep`). If `D = 0` the `≠ 0` condition excludes all
    elements; if `D ≠ 0` then at most `d` values of `cs i` are roots (by
    `card_roots'` + `hD_deg`). Summing over `|F|^(n-1)` fibers gives the bound. -/
theorem countSat_adaptive_root {n : ℕ} {d : ℕ} (i : Fin n)
    (D : RandomChallenges F n → Polynomial F)
    (hD_indep : ∀ cs cs', (∀ j, j ≠ i → cs j = cs' j) → D cs = D cs')
    (hD_deg : ∀ cs, (D cs).natDegree ≤ d) :
    countSat (fun cs => D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) ≤
      d * Fintype.card F ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  simp only [Nat.add_sub_cancel]
  unfold countSat
  -- proj : drop coordinate i
  set proj : RandomChallenges F (m + 1) → (Fin m → F) :=
    fun cs j => cs (i.succAbove j) with proj_def
  set sat := univ.filter (fun cs : RandomChallenges F (m + 1) =>
    D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) with sat_def
  -- Decompose by fiber over proj
  have hfib : sat.card =
      ∑ g ∈ (univ : Finset (Fin m → F)),
        (sat.filter (fun cs => proj cs = g)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := proj)]
    intro cs _hcs
    exact Finset.mem_univ _
  rw [hfib]
  -- Bound each fiber by d, then sum
  calc ∑ g ∈ (univ : Finset (Fin m → F)), (sat.filter (fun cs => proj cs = g)).card
      ≤ ∑ _g ∈ (univ : Finset (Fin m → F)), d :=
        Finset.sum_le_sum (fun g _ => ?fiber_bound)
    _ = d * Fintype.card F ^ m := by
        rw [Finset.sum_const, Finset.card_univ, card_randomChallenges, smul_eq_mul,
            mul_comm]
  case fiber_bound =>
  -- Fix a fiber g : Fin m → F. Show its contribution ≤ d.
  set S := sat.filter (fun cs => proj cs = g) with S_def
  -- Pick a representative: insertNth i 0 g (the value at i doesn't matter for D)
  set rep : Fin (m + 1) → F :=
    Fin.insertNth i (0 : F) (fun j : Fin m => g j) with rep_def
  have hrep_proj : proj rep = g := by
    funext j; simp [proj_def, rep_def, Fin.insertNth_apply_succAbove]
  -- Helper: extract fiber membership
  have mem_S : ∀ cs, cs ∈ S ↔ cs ∈ sat ∧ proj cs = g := by
    intro cs; rw [S_def]; exact Finset.mem_filter
  -- Helper: extract sat membership
  have mem_sat : ∀ cs, cs ∈ sat ↔ cs ∈ univ ∧ (D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) := by
    intro cs; rw [sat_def]; exact Finset.mem_filter
  -- D is constant on the fiber: any cs in S agrees with rep on non-i coords
  have hD_const : ∀ cs, cs ∈ S → D cs = D rep := by
    intro cs hcs
    rw [mem_S] at hcs
    apply hD_indep
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    have h1 : (proj cs) k = g k := congr_fun hcs.2 k
    have h2 : (proj rep) k = g k := congr_fun hrep_proj k
    simp [proj_def] at h1 h2
    rw [h1, h2]
  -- Inject S into roots of D rep via cs ↦ cs i
  by_cases hDrep : D rep = 0
  · -- If D rep = 0 then D cs = 0 for all cs in fiber, so D cs ≠ 0 is impossible
    have : S = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro cs hcs
      have hmem := (mem_S cs).mp hcs
      have hsat := (mem_sat cs).mp hmem.1
      exact hsat.2.1 (hD_const cs hcs ▸ hDrep)
    rw [this, Finset.card_empty]
    exact Nat.zero_le _
  · -- D rep ≠ 0; inject S into roots of D rep
    apply le_trans (Finset.card_le_card_of_injOn (fun cs => cs i) _ _)
    · -- roots bound
      calc (D rep).roots.toFinset.card
          ≤ (D rep).roots.card := Multiset.toFinset_card_le _
        _ ≤ (D rep).natDegree := card_roots' _
        _ ≤ d := hD_deg rep
    · -- MapsTo: each satisfying cs maps to a root
      intro cs hcs
      have hmem := (mem_S cs).mp hcs
      have hsat := (mem_sat cs).mp hmem.1
      have hDeq : D cs = D rep := hD_const cs hcs
      show cs i ∈ (D rep).roots.toFinset
      rw [Multiset.mem_toFinset, mem_roots hDrep]
      exact IsRoot.def.mpr (hDeq ▸ hsat.2.2)
    · -- InjOn: cs in same fiber with same cs i are equal
      intro cs₁ hcs₁ cs₂ hcs₂ heq_i
      have hmem₁ := (mem_S cs₁).mp (Finset.mem_coe.mp hcs₁)
      have hmem₂ := (mem_S cs₂).mp (Finset.mem_coe.mp hcs₂)
      funext j
      by_cases hj : j = i
      · subst hj; exact heq_i
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        have h1 : (proj cs₁) k = g k := congr_fun hmem₁.2 k
        have h2 : (proj cs₂) k = g k := congr_fun hmem₂.2 k
        simp [proj_def] at h1 h2
        rw [h1, h2]

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
