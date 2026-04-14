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
