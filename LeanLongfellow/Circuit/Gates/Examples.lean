import LeanLongfellow.Circuit.Core.Reduction

open Finset MultilinearPoly Polynomial

/-! # Square Root Circuit Example

A minimal end-to-end example: a single mul gate proving
"I know x such that x * x = y."

The circuit has `s = 1` (so each layer has `2^1 = 2` positions).
One mul gate at position 0 connects `V_next(0) * V_next(0) = V_curr(0)`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Circuit and layer definitions
-- ============================================================

/-- The square root circuit: one mul gate at position 0.
    Encodes: `V_curr(0) = V_next(0) * V_next(0)`, i.e., `y = x * x`. -/
noncomputable def sqrtCircuit : CircuitLayer F 1 where
  add_poly := ⟨fun _ => 0⟩
  mul_poly := ⟨fun glr =>
    if glr = (fun _ => false) then 1 else 0⟩

/-- Witness layer: `V_next(0) = x`, `V_next(1) = 0`. -/
noncomputable def sqrtWitness (x : F) : LayerValues F 1 where
  table := fun b => if b (0 : Fin 1) then 0 else x

/-- Output layer: `V_curr(0) = y`, `V_curr(1) = 0`. -/
noncomputable def sqrtOutput (y : F) : LayerValues F 1 where
  table := fun b => if b (0 : Fin 1) then 0 else y

-- ============================================================
-- Section 2: Helper lemmas for small finite types
-- ============================================================

/-- Every `Fin 1 → Bool` equals `fun _ => false` or `fun _ => true`. -/
private theorem fin1_bool_dichotomy (f : Fin 1 → Bool) :
    f = (fun _ => false) ∨ f = (fun _ => true) := by
  rcases hf : f 0 with _ | _
  · left; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf
  · right; funext ⟨i, hi⟩
    have : (⟨i, hi⟩ : Fin 1) = (0 : Fin 1) := Fin.ext (by omega)
    rw [show f ⟨i, hi⟩ = f 0 from congrArg f this]; exact hf

/-- For s=1, `concat3 (fun _ => false) (splitL lr) (splitR lr) = fun _ => false`
    iff `lr = fun _ => false`. -/
private theorem concat3_splitLR_s1 (lr : Fin (2 * 1) → Bool) :
    concat3 (fun _ : Fin 1 => false) (splitL lr) (splitR lr) = (fun _ => false) ↔
    lr = (fun _ => false) := by
  constructor
  · intro heq
    funext ⟨i, hi⟩
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · -- i = 0: comes from splitL at position 0, which is concat3 at position 1
      have h1 := congr_fun heq ⟨1, by omega⟩
      simp [concat3, splitL] at h1
      exact h1
    · -- i = 1: comes from splitR at position 0, which is concat3 at position 2
      have h2 := congr_fun heq ⟨2, by omega⟩
      simp [concat3, splitR] at h2
      exact h2
  · intro hlr; subst hlr
    funext ⟨k, hk⟩
    simp [concat3, splitL, splitR]

/-- `concat3` with `g = fun _ => true` never equals `fun _ => false`. -/
private theorem concat3_true_ne_false (l r : Fin 1 → Bool) :
    concat3 (fun _ : Fin 1 => true) l r ≠ fun _ => false := by
  intro heq
  have := congr_fun heq ⟨0, by omega⟩
  simp [concat3] at this

-- ============================================================
-- Section 3: Layer consistency
-- ============================================================

/-- When `x * x = y`, the square root circuit is layer-consistent. -/
theorem sqrtCircuit_consistent (x y : F) (h : x * x = y) :
    ∀ g, layerConsistent (sqrtCircuit (F := F)) (sqrtOutput y) (sqrtWitness x) g := by
  intro g
  unfold layerConsistent sqrtCircuit sqrtOutput sqrtWitness
  simp only
  rcases fin1_bool_dichotomy g with hg | hg <;> subst hg
  · -- Case g = fun _ => false (output position 0): value should be y
    show y = _
    -- add_poly is always 0
    simp only [zero_mul, zero_add]
    -- Each mul_poly term: (if concat3 ... = false then 1 else 0) * (w(l) * w(r))
    -- Only lr = fun _ => false contributes (x * x).
    have key : ∀ lr : Fin (2 * 1) → Bool,
        (if concat3 (fun _ : Fin 1 => false) (splitL lr) (splitR lr) = fun _ => false
         then (1 : F) else 0) *
        ((if (splitL lr) (0 : Fin 1) then (0 : F) else x) *
         (if (splitR lr) (0 : Fin 1) then (0 : F) else x)) =
        if lr = fun _ => false then x * x else 0 := by
      intro lr
      by_cases hlr : lr = fun _ => false
      · -- lr = fun _ => false: concat3 matches, witness values are both x
        subst hlr
        have hc := (concat3_splitLR_s1 (fun _ => false)).mpr rfl
        simp [hc, splitL, splitR]
      · -- lr ≠ fun _ => false: concat3 doesn't match
        have hconcat : ¬(concat3 (fun _ : Fin 1 => false) (splitL lr) (splitR lr) = fun _ => false) :=
          mt (concat3_splitLR_s1 lr).mp hlr
        simp [hconcat, hlr]
    simp_rw [key]
    rw [Finset.sum_ite_eq']
    simp [h]
  · -- Case g = fun _ => true (output position 1): value should be 0
    show (0 : F) = _
    simp only [zero_mul, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro lr _
    have : ¬(concat3 (fun _ : Fin 1 => true) (splitL lr) (splitR lr) = fun _ => false) :=
      concat3_true_ne_false _ _
    simp [this]

-- ============================================================
-- Section 4: Soundness corollary
-- ============================================================

/-- If someone claims the output is `claimed_y` but `x * x ≠ claimed_y`,
    and the sumcheck verifier accepts, a challenge hit a degree-≤-2 root.

    This is a direct application of `layer_reduction_soundness`. -/
theorem sqrtCircuit_soundness [DecidableEq F] (x y claimed_y : F)
    (h : x * x = y) (hclaim : claimed_y ≠ y)
    (red : LayerReduction F 1)
    (haccept : layerReductionAccepts sqrtCircuit
      (boolToField (fun _ : Fin 1 => false)) claimed_y (sqrtWitness x) red)
    (hdeg : ∀ i, (red.rounds i).prover_poly.natDegree ≤ 2) :
    ∃ i, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 2 ∧
      diff.eval (red.rounds i).challenge = 0 := by
  have hs : 0 < 2 * 1 := by omega
  have hcons := sqrtCircuit_consistent x y h
  have hclaim' : claimed_y ≠ (sqrtOutput (F := F) y).table (fun _ : Fin 1 => false) := by
    simp only [sqrtOutput, Bool.false_eq_true, ite_false]
    exact hclaim
  exact layer_reduction_soundness sqrtCircuit (fun _ => false) claimed_y
    (sqrtOutput y) (sqrtWitness x) red hs hcons hclaim' haccept hdeg
