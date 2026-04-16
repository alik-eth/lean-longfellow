import LeanLongfellow.Circuit.Gates.Defs
import LeanLongfellow.Circuit.Gates.Gadgets
import LeanLongfellow.Circuit.Gates.Word32
import LeanLongfellow.Circuit.Gates.Examples

open Finset MultilinearPoly

set_option autoImplicit false

/-! # Gadget-to-Gate Bridge

Connects field-level gadget constraints (from `Gadgets.lean`) to the circuit
layer model (from `Gates.lean`). The two key results are:

1. **Gate semantics**: a single mul/add gate in a layer yields `layerConsistent`
   iff the expected field equation holds on the wire values.
2. **Gadget decompositions**: each compound gadget (isBool, boolXor, etc.)
   factors into field equations that individual gates can enforce.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Helpers for gate matching
-- ============================================================

/-- Build the canonical `Fin (2*s) → Bool` from separate `l` and `r` vectors. -/
private def buildLR {s : ℕ} (l r : Fin s → Bool) : Fin (2 * s) → Bool :=
  fun k => if h : k.val < s then l ⟨k.val, h⟩ else r ⟨k.val - s, by omega⟩

@[simp] private theorem splitL_buildLR {s : ℕ} (l r : Fin s → Bool) :
    splitL (buildLR l r) = l := by
  funext j; simp [splitL, buildLR, j.isLt]

@[simp] private theorem splitR_buildLR {s : ℕ} (l r : Fin s → Bool) :
    splitR (buildLR l r) = r := by
  funext j; simp [splitR, buildLR, show ¬(j.val + s < s) by omega]

private theorem buildLR_unique {s : ℕ} {l r : Fin s → Bool}
    {lr : Fin (2 * s) → Bool} (hL : splitL lr = l) (hR : splitR lr = r) :
    lr = buildLR l r := by
  funext k; simp only [buildLR]
  by_cases hk : k.val < s
  · simp [hk]; have := congrFun hL ⟨k.val, hk⟩; simp [splitL] at this; exact this
  · simp [hk]
    have := congrFun hR ⟨k.val - s, by omega⟩
    simp [splitR] at this; convert this using 2; apply Fin.ext; simp; omega

-- ============================================================
-- Section 2: Single-gate layer semantics
-- ============================================================

/-- A single mul gate `(g, l, r)` gives `layerConsistent` at all positions iff
    `V_curr(g) = V_next(l) * V_next(r)` and all other positions are zero. -/
theorem single_mul_gate_consistent {s : ℕ}
    (g l r : Fin s → Bool) (V_curr V_next : LayerValues F s) :
    (∀ g', layerConsistent (gatesToLayer F [⟨.mul, g, l, r⟩]) V_curr V_next g') ↔
    V_curr.table g = V_next.table l * V_next.table r ∧
    ∀ g', g' ≠ g → V_curr.table g' = 0 := by
  constructor
  · -- Forward: extract equations from layerConsistent
    intro hall
    constructor
    · -- At the gate position
      have hg := hall g
      simp only [layerConsistent, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false,
                  splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      have off : ∀ lr ∈ Finset.univ, lr ≠ buildLR l r →
          (if (⟨GateType.mul, g, l, r⟩ : Gate s).matches .add g (splitL lr) (splitR lr) = true
           then (1 : F) else 0) * (V_next.table (splitL lr) + V_next.table (splitR lr)) +
          (if (⟨GateType.mul, g, l, r⟩ : Gate s).matches .mul g (splitL lr) (splitR lr) = true
           then (1 : F) else 0) * (V_next.table (splitL lr) * V_next.table (splitR lr)) = 0 := by
        intro lr _ hlr
        have hlr' : splitL lr ≠ l ∨ splitR lr ≠ r := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hadd : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .add g (splitL lr) (splitR lr) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
          exact absurd h.1 GateType.noConfusion
        have hmul : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .mul g (splitL lr) (splitR lr) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
          rcases hlr' with hl | hr
          · exact hl h.2.2.1.symm
          · exact hr h.2.2.2.symm
        simp [hadd, hmul]
      rw [Finset.sum_eq_single (buildLR l r) off (by simp)]
      simp only [splitL_buildLR, splitR_buildLR]
      have hadd : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .add g l r = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact absurd h.1 GateType.noConfusion
      have hmul : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .mul g l r = true := by
        rw [Gate.matches_iff]; exact ⟨rfl, rfl, rfl, rfl⟩
      simp [hadd, hmul]
    · -- At other positions: everything is zero
      intro g' hg'
      have hcons := hall g'
      simp only [layerConsistent, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false,
                  splitG_concat3, splitLG_concat3, splitRG_concat3] at hcons
      rw [hcons]
      apply Finset.sum_eq_zero; intro lr _
      have hadd : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .add g' (splitL lr) (splitR lr) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact absurd h.1 GateType.noConfusion
      have hmul : (⟨GateType.mul, g, l, r⟩ : Gate s).matches .mul g' (splitL lr) (splitR lr) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact hg' h.2.1.symm
      simp [hadd, hmul]
  · -- Backward: use gatesToLayer_consistent
    intro ⟨hgate, hcov⟩
    apply gatesToLayer_consistent
    · intro gate hmem; simp at hmem; subst hmem; exact hgate
    · intro g'; simp only [List.filter_cons, List.filter_nil]; split <;> simp
    · intro g' hg'
      simp only [List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hg'
      exact hcov g' (fun h => hg' h.symm)

/-- A single add gate `(g, l, r)` gives `layerConsistent` at all positions iff
    `V_curr(g) = V_next(l) + V_next(r)` and all other positions are zero. -/
theorem single_add_gate_consistent {s : ℕ}
    (g l r : Fin s → Bool) (V_curr V_next : LayerValues F s) :
    (∀ g', layerConsistent (gatesToLayer F [⟨.add, g, l, r⟩]) V_curr V_next g') ↔
    V_curr.table g = V_next.table l + V_next.table r ∧
    ∀ g', g' ≠ g → V_curr.table g' = 0 := by
  constructor
  · intro hall
    constructor
    · have hg := hall g
      simp only [layerConsistent, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false,
                  splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      have off : ∀ lr ∈ Finset.univ, lr ≠ buildLR l r →
          (if (⟨GateType.add, g, l, r⟩ : Gate s).matches .add g (splitL lr) (splitR lr) = true
           then (1 : F) else 0) * (V_next.table (splitL lr) + V_next.table (splitR lr)) +
          (if (⟨GateType.add, g, l, r⟩ : Gate s).matches .mul g (splitL lr) (splitR lr) = true
           then (1 : F) else 0) * (V_next.table (splitL lr) * V_next.table (splitR lr)) = 0 := by
        intro lr _ hlr
        have hlr' : splitL lr ≠ l ∨ splitR lr ≠ r := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hadd : (⟨GateType.add, g, l, r⟩ : Gate s).matches .add g (splitL lr) (splitR lr) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
          rcases hlr' with hl | hr
          · exact hl h.2.2.1.symm
          · exact hr h.2.2.2.symm
        have hmul : (⟨GateType.add, g, l, r⟩ : Gate s).matches .mul g (splitL lr) (splitR lr) = false := by
          rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
          exact absurd h.1 GateType.noConfusion
        simp [hadd, hmul]
      rw [Finset.sum_eq_single (buildLR l r) off (by simp)]
      simp only [splitL_buildLR, splitR_buildLR]
      have hadd : (⟨GateType.add, g, l, r⟩ : Gate s).matches .add g l r = true := by
        rw [Gate.matches_iff]; exact ⟨rfl, rfl, rfl, rfl⟩
      have hmul : (⟨GateType.add, g, l, r⟩ : Gate s).matches .mul g l r = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact absurd h.1 GateType.noConfusion
      simp [hadd, hmul]
    · intro g' hg'
      have hcons := hall g'
      simp only [layerConsistent, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false,
                  splitG_concat3, splitLG_concat3, splitRG_concat3] at hcons
      rw [hcons]
      apply Finset.sum_eq_zero; intro lr _
      have hadd : (⟨GateType.add, g, l, r⟩ : Gate s).matches .add g' (splitL lr) (splitR lr) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact hg' h.2.1.symm
      have hmul : (⟨GateType.add, g, l, r⟩ : Gate s).matches .mul g' (splitL lr) (splitR lr) = false := by
        rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
        exact absurd h.1 GateType.noConfusion
      simp [hadd, hmul]
  · intro ⟨hgate, hcov⟩
    apply gatesToLayer_consistent
    · intro gate hmem; simp at hmem; subst hmem; exact hgate
    · intro g'; simp only [List.filter_cons, List.filter_nil]; split <;> simp
    · intro g' hg'
      simp only [List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq] at hg'
      exact hcov g' (fun h => hg' h.symm)

-- ============================================================
-- Section 3: Gadget decompositions into gate-level operations
-- ============================================================

/-- `isBool x` decomposes into a complement witness and a mul-equals-zero
    check. If `y` witnesses `1 - x` (enforced by an add gate: `x + y = 1`)
    and a mul gate computes `p = x * y`, then `isBool x ↔ p = 0`. -/
theorem isBool_as_circuit (x y p : F) (hsum : x + y = 1) (hprod : p = x * y) :
    isBool x ↔ p = 0 := by
  have hy : y = 1 - x := by
    have h := hsum
    rw [show x + y = 1 ↔ y = 1 - x from ⟨fun h => by rw [← h]; ring,
                                           fun h => by rw [h]; ring⟩] at h
    exact h
  subst hprod; rw [hy]; rfl

/-- `boolAnd a b r` is exactly the statement that `a` and `b` are boolean
    and `r = a * b`. This is one mul gate (given boolean inputs). -/
theorem boolAnd_as_mul_gate (a b r : F) :
    boolAnd a b r ↔ isBool a ∧ isBool b ∧ r = a * b := by
  unfold boolAnd; tauto

/-- `boolXor a b r` decomposes into: one mul gate (`t = a * b`),
    and the field identity `r = a + b - 2 * t`. -/
theorem boolXor_decomposition (a b t r : F)
    (ha : isBool a) (hb : isBool b)
    (hmul : t = a * b)
    (hresult : r = a + b - 2 * t) :
    boolXor a b r := by
  refine ⟨ha, hb, ?_, ?_⟩
  · rw [hresult, hmul]; unfold isBool
    rcases (isBool_iff a).mp ha with rfl | rfl <;>
    rcases (isBool_iff b).mp hb with rfl | rfl <;> ring
  · rw [hresult, hmul]; ring

/-- Converse: if `boolXor a b r` holds, we can extract the intermediate
    product `t = a * b` and the linear relation `r = a + b - 2 * t`. -/
theorem boolXor_to_gates (a b r : F) (h : boolXor a b r) :
    ∃ t, t = a * b ∧ r = a + b - 2 * t :=
  ⟨a * b, rfl, by rw [h.2.2.2]; ring⟩

/-- `condSelect b x y result` decomposes into two mul gates and one add gate:
    `t₁ = b * x`, `t₂ = (1 - b) * y`, `result = t₁ + t₂`. -/
theorem condSelect_decomposition (b x y t₁ t₂ result : F)
    (hb : isBool b)
    (hmul1 : t₁ = b * x) (hmul2 : t₂ = (1 - b) * y)
    (hadd : result = t₁ + t₂) :
    condSelect b x y result :=
  ⟨hb, by rw [hadd, hmul1, hmul2]⟩

/-- `word32Add`'s constraint is equivalent to boolean witnesses for `c` and
    `carry`, plus a single linear equation over the wire values. -/
theorem word32Add_as_linear_constraint (a b c : Fin 32 → F) (carry : F) :
    word32Add a b c carry ↔
    isWord32 c ∧ isBool carry ∧
    word32Val a + word32Val b = word32Val c + carry * (2 : F) ^ 32 := by
  unfold word32Add; exact Iff.rfl

-- ============================================================
-- Section 4: Square root example via the gate bridge
-- ============================================================

/-- The square root circuit from `Examples.lean` matches the `gatesToLayer`
    output for a single mul gate at position 0 (all-false wires).

    This shows the hand-built `sqrtCircuit` is exactly what `gatesToLayer`
    produces, connecting the ad-hoc and systematic circuit constructions. -/
theorem sqrtCircuit_eq_gatesToLayer :
    @sqrtCircuit F _ = gatesToLayer F [⟨.mul,
      (fun _ : Fin 1 => false), (fun _ : Fin 1 => false), (fun _ : Fin 1 => false)⟩] := by
  -- We prove pointwise equality of the add/mul polynomial tables.
  have gate0_add_false : ∀ glr : Fin (3 * 1) → Bool,
      (⟨GateType.mul, fun _ : Fin 1 => false, fun _ : Fin 1 => false,
        fun _ : Fin 1 => false⟩ : Gate 1).matches .add
        (splitG glr) (splitLG glr) (splitRG glr) = false := by
    intro glr; rw [Bool.eq_false_iff]; intro h; rw [Gate.matches_iff] at h
    exact absurd h.1 GateType.noConfusion
  have gate0_mul_iff : ∀ glr : Fin (3 * 1) → Bool,
      (⟨GateType.mul, fun _ : Fin 1 => false, fun _ : Fin 1 => false,
        fun _ : Fin 1 => false⟩ : Gate 1).matches .mul
        (splitG glr) (splitLG glr) (splitRG glr) = true ↔
      glr = fun _ => false := by
    intro glr; rw [Gate.matches_iff]
    constructor
    · intro ⟨_, hg, hl, hr⟩
      have hg' : splitG glr = fun _ => false := hg.symm
      have hl' : splitLG glr = fun _ => false := hl.symm
      have hr' : splitRG glr = fun _ => false := hr.symm
      rw [← concat3_splitG_splitLG_splitRG glr, hg', hl', hr']
      funext ⟨k, hk⟩; simp [concat3]
    · intro h; rw [h]
      exact ⟨rfl, by funext j; simp [splitG],
             by funext j; simp [splitLG],
             by funext j; simp [splitRG]⟩
  -- Prove sqrtCircuit = gatesToLayer by showing both structures agree
  have htable_add : ∀ glr, (sqrtCircuit (F := F)).add_poly.table glr =
      (gatesToLayer F [⟨.mul, fun _ : Fin 1 => false, fun _ : Fin 1 => false,
        fun _ : Fin 1 => false⟩]).add_poly.table glr := by
    intro glr
    simp only [sqrtCircuit, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false]
    rw [gate0_add_false]; rfl
  have htable_mul : ∀ glr, (sqrtCircuit (F := F)).mul_poly.table glr =
      (gatesToLayer F [⟨.mul, fun _ : Fin 1 => false, fun _ : Fin 1 => false,
        fun _ : Fin 1 => false⟩]).mul_poly.table glr := by
    intro glr
    simp only [sqrtCircuit, gatesToLayer, List.any_cons, List.any_nil, Bool.or_false]
    by_cases h : glr = fun _ => false
    · rw [h, (gate0_mul_iff _).mpr rfl]; rfl
    · rw [show _ = false from Bool.eq_false_iff.mpr (mt (gate0_mul_iff glr).mp h)]
      simp [h]
  show CircuitLayer.mk _ _ = CircuitLayer.mk _ _
  congr 1 ; exact congrArg MultilinearPoly.mk (funext (by assumption))
