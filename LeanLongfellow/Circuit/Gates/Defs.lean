import LeanLongfellow.Circuit.Defs

open Finset MultilinearPoly

set_option autoImplicit false

/-! # Gate-level Circuit Representation Bridge

Maps concrete gate descriptions (add/mul with Boolean-vector indices)
to the abstract `CircuitLayer` model with multilinear indicator polynomials.
-/

-- ============================================================
-- Section 1: Gate types
-- ============================================================

/-- The two gate types in an arithmetic circuit. -/
inductive GateType where
  | add
  | mul
  deriving DecidableEq, BEq

/-- A gate in a layer with `2^s` positions, indexed by Boolean vectors of length `s`. -/
structure Gate (s : ℕ) where
  gateType : GateType
  output : Fin s → Bool
  left : Fin s → Bool
  right : Fin s → Bool

-- ============================================================
-- Section 2: Splitting a 3s-vector into (g, l, r)
-- ============================================================

/-- Extract the first s bits (gate index) from a 3s-vector. -/
def splitG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val, by omega⟩

/-- Extract the middle s bits (left input) from a 3s-vector. -/
def splitLG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val + s, by omega⟩

/-- Extract the last s bits (right input) from a 3s-vector. -/
def splitRG {s : ℕ} (glr : Fin (3 * s) → Bool) : Fin s → Bool :=
  fun j => glr ⟨j.val + 2 * s, by omega⟩

-- ============================================================
-- Section 3: Split/concat round-trip lemmas
-- ============================================================

@[simp] theorem splitG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitG (concat3 g l r) = g := by
  funext j
  simp [splitG, concat3, j.isLt]

@[simp] theorem splitLG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitLG (concat3 g l r) = l := by
  funext j
  simp only [splitLG, concat3]
  have h1 : ¬(j.val + s < s) := by omega
  have h2 : j.val + s < 2 * s := by omega
  simp [h1, h2, show j.val + s - s = j.val by omega]

@[simp] theorem splitRG_concat3 {s : ℕ} (g l r : Fin s → Bool) :
    splitRG (concat3 g l r) = r := by
  funext j
  simp only [splitRG, concat3]
  have h1 : ¬(j.val + 2 * s < s) := by omega
  have h2 : ¬(j.val + 2 * s < 2 * s) := by omega
  simp [h1, h2, show j.val + 2 * s - 2 * s = j.val by omega]

@[simp] theorem concat3_splitG_splitLG_splitRG {s : ℕ} (glr : Fin (3 * s) → Bool) :
    concat3 (splitG glr) (splitLG glr) (splitRG glr) = glr := by
  funext ⟨k, hk⟩
  simp only [concat3, splitG, splitLG, splitRG]
  split
  case isTrue h => rfl
  case isFalse h1 =>
    split
    case isTrue h2 =>
      have : (⟨k - s + s, by omega⟩ : Fin (3 * s)) = ⟨k, hk⟩ := by
        apply Fin.ext; simp; omega
      rw [this]
    case isFalse h2 =>
      have : (⟨k - 2 * s + 2 * s, by omega⟩ : Fin (3 * s)) = ⟨k, hk⟩ := by
        apply Fin.ext; simp; omega
      rw [this]

-- ============================================================
-- Section 4: Gate matching
-- ============================================================

/-- Does a gate match position (g, l, r) with the given type? -/
def Gate.matches {s : ℕ} (gate : Gate s) (ty : GateType) (g l r : Fin s → Bool) : Bool :=
  decide (gate.gateType = ty) && decide (gate.output = g) &&
  decide (gate.left = l) && decide (gate.right = r)

theorem Gate.matches_iff {s : ℕ} (gate : Gate s) (ty : GateType) (g l r : Fin s → Bool) :
    gate.matches ty g l r = true ↔
    gate.gateType = ty ∧ gate.output = g ∧ gate.left = l ∧ gate.right = r := by
  simp [Gate.matches, Bool.and_eq_true, decide_eq_true_eq]
  tauto

-- ============================================================
-- Section 5: Building a CircuitLayer from gates
-- ============================================================

/-- Build a `CircuitLayer` from a list of gates.
    `add_poly.table(g,l,r) = 1` if there is an add gate `(g,l,r)`, else `0`.
    `mul_poly.table(g,l,r) = 1` if there is a mul gate `(g,l,r)`, else `0`. -/
def gatesToLayer {s : ℕ} (F : Type*) [Field F] (gates : List (Gate s)) :
    CircuitLayer F s where
  add_poly := ⟨fun glr =>
    if gates.any (fun gate => gate.matches .add (splitG glr) (splitLG glr) (splitRG glr))
    then 1 else 0⟩
  mul_poly := ⟨fun glr =>
    if gates.any (fun gate => gate.matches .mul (splitG glr) (splitLG glr) (splitRG glr))
    then 1 else 0⟩

-- ============================================================
-- Section 6: Correctness theorem
-- ============================================================

/-- If each gate is correctly evaluated, each output position has at most one gate,
    and uncovered positions have value 0, then `layerConsistent` holds. -/
theorem gatesToLayer_consistent {s : ℕ} {F : Type*} [Field F]
    (gates : List (Gate s))
    (V_curr V_next : LayerValues F s)
    -- Each gate is correctly evaluated
    (heval : ∀ gate ∈ gates, match gate.gateType with
      | .add => V_curr.table gate.output =
                V_next.table gate.left + V_next.table gate.right
      | .mul => V_curr.table gate.output =
                V_next.table gate.left * V_next.table gate.right)
    -- Each output position has at most one gate
    (huniq : ∀ g : Fin s → Bool,
      (gates.filter (fun gate => decide (gate.output = g))).length ≤ 1)
    -- Uncovered output positions have value 0
    (hcovered : ∀ g : Fin s → Bool,
      (¬ gates.any (fun gate => decide (gate.output = g))) →
      V_curr.table g = 0)
    (g : Fin s → Bool) :
    layerConsistent (gatesToLayer F gates) V_curr V_next g := by
  simp only [layerConsistent, gatesToLayer, splitG_concat3, splitLG_concat3, splitRG_concat3]
  -- Helper: uniqueness of gates with output = g
  have gate_unique : ∀ g₁ g₂ : Gate s, g₁ ∈ gates → g₂ ∈ gates →
      g₁.output = g → g₂.output = g → g₁ = g₂ := by
    intro g₁ g₂ hg₁ hg₂ ho₁ ho₂
    have hg₁f : g₁ ∈ gates.filter (fun gate => decide (gate.output = g)) := by
      simp [List.mem_filter, hg₁, ho₁]
    have hg₂f : g₂ ∈ gates.filter (fun gate => decide (gate.output = g)) := by
      simp [List.mem_filter, hg₂, ho₂]
    have hlen : (gates.filter (fun gate => decide (gate.output = g))).length = 1 := by
      have := huniq g
      have := List.length_pos_of_mem hg₁f
      omega
    obtain ⟨x, t, hxt⟩ := (gates.filter (fun gate => decide (gate.output = g))).exists_of_length_succ
      (n := 0) hlen
    rw [hxt] at hlen
    simp at hlen
    rw [hxt, hlen] at hg₁f hg₂f
    simp at hg₁f hg₂f
    rw [hg₁f, hg₂f]
  -- Helper: if no gate has output=g, then no gate matches (g,l,r) for any type
  have no_match_of_no_output : ∀ (ty : GateType) (l r : Fin s → Bool),
      ¬ (gates.any (fun gate => decide (gate.output = g)) = true) →
      (gates.any (fun gate => gate.matches ty g l r)) = false := by
    intro ty l r hno
    rw [List.any_eq_false]
    intro gate hgate_mem
    rw [Gate.matches_iff]
    intro ⟨_, hout, _, _⟩
    apply hno
    rw [List.any_eq_true]
    exact ⟨gate, hgate_mem, by simp [hout]⟩
  -- Helper: any gate matching at (g, l, r) must be the unique gate with output g
  have no_match_wrong_lr : ∀ (ty : GateType) (l r : Fin s → Bool) (gate0 : Gate s),
      gate0 ∈ gates → gate0.output = g →
      (l ≠ gate0.left ∨ r ≠ gate0.right) →
      (gates.any (fun gate' => gate'.matches ty g l r)) = false := by
    intro ty l r gate0 hmem0 hout0 hlr_ne
    rw [List.any_eq_false]
    intro gate' hgate'_mem
    rw [Gate.matches_iff]
    intro ⟨_, hout', hleft', hright'⟩
    have := gate_unique gate' gate0 hgate'_mem hmem0 hout' hout0
    subst this
    rcases hlr_ne with hl | hr
    · exact hl hleft'.symm
    · exact hr hright'.symm
  -- Case split: is g covered by some gate?
  by_cases hany : gates.any (fun gate => decide (gate.output = g)) = true
  · -- Case 1: g is covered by at least one gate
    rw [List.any_eq_true] at hany
    obtain ⟨gate, hgate_mem, hgate_out⟩ := hany
    simp only [decide_eq_true_eq] at hgate_out
    -- Build the lr pair for this gate
    let lr₀ : Fin (2 * s) → Bool := fun k =>
      if h : k.val < s then gate.left ⟨k.val, h⟩
      else gate.right ⟨k.val - s, by omega⟩
    have hlr₀L : splitL lr₀ = gate.left := by
      funext j; simp [splitL, lr₀, j.isLt]
    have hlr₀R : splitR lr₀ = gate.right := by
      funext j; simp [splitR, lr₀, show ¬(j.val + s < s) by omega]
    -- Inverse: splitL/splitR determine lr
    have lr_eq_of_splits : ∀ lr : Fin (2 * s) → Bool,
        splitL lr = gate.left → splitR lr = gate.right → lr = lr₀ := by
      intro lr hL hR
      funext k
      simp only [lr₀]
      by_cases hk : k.val < s
      · simp [hk]
        have := congrFun hL ⟨k.val, hk⟩
        simp [splitL] at this
        exact this
      · simp [hk]
        have hk2 := k.isLt
        have := congrFun hR ⟨k.val - s, by omega⟩
        simp [splitR] at this
        convert this using 2
        apply Fin.ext; simp; omega
    -- For lr ≠ lr₀, both match functions return false
    have off_diag : ∀ lr ∈ Finset.univ, lr ≠ lr₀ →
        (if (gates.any fun g' => g'.matches .add g (splitL lr) (splitR lr)) then (1 : F) else 0) *
          (V_next.table (splitL lr) + V_next.table (splitR lr)) +
        (if (gates.any fun g' => g'.matches .mul g (splitL lr) (splitR lr)) then (1 : F) else 0) *
          (V_next.table (splitL lr) * V_next.table (splitR lr)) = 0 := by
      intro lr _ hlr_ne
      have hlr_diff : splitL lr ≠ gate.left ∨ splitR lr ≠ gate.right := by
        by_contra h
        push Not at h
        exact hlr_ne (lr_eq_of_splits lr h.1 h.2)
      have hadd := no_match_wrong_lr .add (splitL lr) (splitR lr) gate hgate_mem hgate_out hlr_diff
      have hmul := no_match_wrong_lr .mul (splitL lr) (splitR lr) gate hgate_mem hgate_out hlr_diff
      simp [hadd, hmul]
    -- Use sum_eq_single to isolate the lr₀ term
    rw [Finset.sum_eq_single lr₀ off_diag (by simp)]
    -- Now the goal is about lr₀ specifically
    rw [hlr₀L, hlr₀R]
    -- Handle the gate type
    have heval_gate := heval gate hgate_mem
    rw [hgate_out] at heval_gate
    -- Helper: no other gate type matches at (g, gate.left, gate.right)
    have no_other_type : ∀ (ty : GateType), gate.gateType ≠ ty →
        (gates.any (fun g' => g'.matches ty g gate.left gate.right)) = false := by
      intro ty hne
      rw [List.any_eq_false]
      intro g' hg'_mem
      rw [Gate.matches_iff]
      intro ⟨hty', hout', _, _⟩
      have := gate_unique g' gate hg'_mem hgate_mem hout' hgate_out
      subst this; exact hne hty'
    -- The gate itself matches
    have self_match : ∀ (ty : GateType), gate.gateType = ty →
        (gates.any (fun g' => g'.matches ty g gate.left gate.right)) = true := by
      intro ty hty
      rw [List.any_eq_true]
      exact ⟨gate, hgate_mem, by rw [Gate.matches_iff]; exact ⟨hty, hgate_out, rfl, rfl⟩⟩
    cases hty : gate.gateType
    · -- add gate
      rw [self_match .add hty, no_other_type .mul (by rw [hty]; decide)]
      simp [hty] at heval_gate
      simp [heval_gate]
    · -- mul gate
      rw [no_other_type .add (by rw [hty]; decide), self_match .mul hty]
      simp [hty] at heval_gate
      simp [heval_gate]
  · -- Case 2: g is not covered - V_curr.table g = 0 and sum = 0
    rw [hcovered g hany]
    symm
    apply Finset.sum_eq_zero
    intro lr _
    have hadd := no_match_of_no_output .add (splitL lr) (splitR lr) hany
    have hmul := no_match_of_no_output .mul (splitL lr) (splitR lr) hany
    simp [hadd, hmul]
