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
- `countSat_root_hit`: a nonzero degree-≤-1 polynomial vanishes on at most
  `|F|^(n-1)` challenge vectors at any given coordinate.
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

/-- If `D(cs)` depends on all coordinates except `i`, has degree ≤ 1, and we count
    the `cs` where `D(cs) ≠ 0` and `D(cs).eval(cs i) = 0`, the count is ≤ `|F|^(n-1)`.

    Proof: split by the `n-1` coordinates other than `i`. For each such fiber,
    `D` is constant (by `hD_indep`). If `D = 0` the `≠ 0` condition fails;
    if `D ≠ 0` at most one value of `cs i` is a root. So each fiber contributes
    at most 1, and there are `|F|^(n-1)` fibers. -/
theorem countSat_adaptive_root {n : ℕ} (i : Fin n)
    (D : RandomChallenges F n → Polynomial F)
    (hD_indep : ∀ cs cs', (∀ j, j ≠ i → cs j = cs' j) → D cs = D cs')
    (hD_deg : ∀ cs, (D cs).natDegree ≤ 1) :
    countSat (fun cs => D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) ≤
      Fintype.card F ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  simp only [Nat.add_sub_cancel]
  -- Inject the satisfying set into (Fin m → F) by dropping coordinate i.
  -- Since |Fin m → F| = |F|^m, this gives the bound.
  rw [show Fintype.card F ^ m = (Finset.univ : Finset (Fin m → F)).card from
      by rw [Finset.card_univ, card_randomChallenges]]
  unfold countSat
  apply Finset.card_le_card_of_injOn
    (fun cs => fun j => cs (i.succAbove j))
    (fun _ _ => Finset.mem_univ _)
  -- Injectivity: if two satisfying cs agree on all coords ≠ i, they must agree on i too
  -- because D(cs) is the same nonzero polynomial and both cs i are roots, but deg ≤ 1
  -- means at most 1 root.
  intro cs₁ hcs₁ cs₂ hcs₂ heq
  simp only [Finset.mem_coe, Finset.mem_filter] at hcs₁ hcs₂
  have hcs₁_sat := hcs₁.2
  have hcs₂_sat := hcs₂.2
  -- cs₁ and cs₂ agree on all coords ≠ i
  have hagree : ∀ j, j ≠ i → cs₁ j = cs₂ j := by
    intro j hj
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    exact congr_fun heq k
  -- D cs₁ = D cs₂ (by independence)
  have hDeq : D cs₁ = D cs₂ := hD_indep cs₁ cs₂ hagree
  -- Both cs₁ i and cs₂ i are roots of D cs₁, which is nonzero with deg ≤ 1
  have hne : D cs₁ ≠ 0 := hcs₁_sat.1
  have hroot₁ : (D cs₁).IsRoot (cs₁ i) := Polynomial.IsRoot.def.mpr hcs₁_sat.2
  have hroot₂ : (D cs₁).IsRoot (cs₂ i) := Polynomial.IsRoot.def.mpr (hDeq ▸ hcs₂_sat.2)
  -- A nonzero poly of degree ≤ 1 has at most 1 root
  have hdeg₁ := hD_deg cs₁
  have hcard : (D cs₁).roots.toFinset.card ≤ 1 := by
    calc (D cs₁).roots.toFinset.card
        ≤ (D cs₁).roots.card := Multiset.toFinset_card_le _
      _ ≤ (D cs₁).natDegree := card_roots' _
      _ ≤ 1 := hdeg₁
  have hmem₁ : cs₁ i ∈ (D cs₁).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hne).mpr hroot₁)
  have hmem₂ : cs₂ i ∈ (D cs₁).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots hne).mpr hroot₂)
  have heq_i : cs₁ i = cs₂ i := by
    have : (D cs₁).roots.toFinset.card ≤ 1 := hcard
    have hsub : {cs₁ i, cs₂ i} ⊆ (D cs₁).roots.toFinset :=
      Finset.insert_subset_iff.mpr ⟨hmem₁, Finset.singleton_subset_iff.mpr hmem₂⟩
    by_contra hne_val
    have : 2 ≤ (D cs₁).roots.toFinset.card := by
      calc 2 = ({cs₁ i, cs₂ i} : Finset F).card := by
            rw [Finset.card_pair hne_val]
        _ ≤ (D cs₁).roots.toFinset.card := Finset.card_le_card hsub
    omega
  funext j
  by_cases hj : j = i
  · subst hj; exact heq_i
  · exact hagree j hj

/-- A nonzero polynomial of degree ≤ 1 vanishes on at most `|F|^(n-1)` challenge
    vectors at any given coordinate. -/
theorem countSat_root_hit {n : ℕ} (i : Fin n)
    {d : Polynomial F} (hd : d ≠ 0) (hdeg : d.natDegree ≤ 1) :
    countSat (fun cs : RandomChallenges F n => d.eval (cs i) = 0) ≤
      Fintype.card F ^ (n - 1) := by
  have hroots : d.roots.toFinset.card ≤ 1 := by
    calc d.roots.toFinset.card
        ≤ d.roots.card := Multiset.toFinset_card_le _
      _ ≤ d.natDegree := card_roots' d
      _ ≤ 1 := hdeg
  have hsub : univ.filter (fun cs : RandomChallenges F n => d.eval (cs i) = 0) ⊆
      d.roots.toFinset.biUnion
        (fun r => univ.filter (fun cs : RandomChallenges F n => cs i = r)) := by
    intro cs hcs
    rw [mem_filter] at hcs
    rw [mem_biUnion]
    have hroot : d.IsRoot (cs i) := IsRoot.def.mpr hcs.2
    exact ⟨cs i, Multiset.mem_toFinset.mpr ((mem_roots hd).mpr hroot),
           mem_filter.mpr ⟨mem_univ cs, rfl⟩⟩
  calc (univ.filter (fun cs => d.eval (cs i) = 0)).card
      ≤ (d.roots.toFinset.biUnion
          (fun r => univ.filter (fun cs : RandomChallenges F n => cs i = r))).card :=
        card_le_card hsub
    _ ≤ ∑ r ∈ d.roots.toFinset,
          (univ.filter (fun cs : RandomChallenges F n => cs i = r)).card :=
        card_biUnion_le
    _ = ∑ _r ∈ d.roots.toFinset, Fintype.card F ^ (n - 1) := by
        congr 1; ext r; exact countSat_eq_val i r
    _ = d.roots.toFinset.card * Fintype.card F ^ (n - 1) := by
        simp [Finset.sum_const]
    _ ≤ 1 * Fintype.card F ^ (n - 1) :=
        Nat.mul_le_mul_right _ hroots
    _ = Fintype.card F ^ (n - 1) := one_mul _
