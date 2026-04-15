import LeanLongfellow.Circuit.Gates

open Finset MultilinearPoly

set_option autoImplicit false

/-! # Gate-level Circuit Infrastructure for s = 5

Universal building blocks for gate-level circuits with `s = 5` (32 wire positions
per layer). Provides wire position definitions, `mulPassLayer` construction, and
the key `mulPassLayer_iff` bidirectional semantics theorem.
-/

-- ============================================================
-- Section 1: Wire position definitions
-- ============================================================

/-- Convert a natural number to its 5-bit little-endian Boolean vector. -/
def wirePos (n : ℕ) : Fin 5 → Bool :=
  fun i => n.testBit i.val

-- Named wire positions (32 total, for s = 5)
def W_ZERO      := wirePos 0
def W_SINV      := wirePos 1
def W_U1        := wirePos 2
def W_U2        := wirePos 3
def W_ACC_X     := wirePos 4
def W_ACC_Y     := wirePos 5
def W_ACC_INF   := wirePos 6
def W_DBL_X     := wirePos 7
def W_DBL_Y     := wirePos 8
def W_DBL_INF   := wirePos 9
def W_PX        := wirePos 10
def W_PY        := wirePos 11
def W_BIT       := wirePos 12
def W_LAMBDA_D  := wirePos 13
def W_LAMBDA_A  := wirePos 14
def W_TEMP1     := wirePos 15
def W_TEMP2     := wirePos 16
def W_TEMP3     := wirePos 17
def W_P1_X      := wirePos 18
def W_P1_Y      := wirePos 19
def W_P1_INF    := wirePos 20
def W_P2_X      := wirePos 21
def W_P2_Y      := wirePos 22
def W_P2_INF    := wirePos 23
def W_FINAL_X   := wirePos 24
def W_FINAL_Y   := wirePos 25
def W_FINAL_INF := wirePos 26
def W_FINAL_LAM := wirePos 27
def W_TEMP4     := wirePos 28
def W_TEMP5     := wirePos 29
def W_ZCHECK    := wirePos 30
def W_OUTPUT    := wirePos 31

/-- `wirePos` is injective on the range 0..31: distinct indices give distinct positions. -/
theorem wirePos_injective : ∀ (a b : Fin 32), wirePos a.val = wirePos b.val → a = b := by
  native_decide

-- ============================================================
-- Section 2: mulPassLayer definition
-- ============================================================

variable (F : Type*) [Field F]

/-- The gate list for a mulPassLayer: one mul gate followed by pass-through add gates. -/
def mulPassGates (out left right : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool)) : List (Gate 5) :=
  (⟨.mul, out, left, right⟩ : Gate 5) ::
    passthroughs.map (fun p => (⟨.add, p, p, W_ZERO⟩ : Gate 5))

/-- Build a layer with one mul gate at `(out, left, right)` and pass-through
    (identity) gates for each position in `passthroughs`. A pass-through gate
    is an add gate `⟨.add, p, p, W_ZERO⟩` which computes `V_next(p) + V_next(W_ZERO)`. -/
def mulPassLayer (out left right : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool)) : CircuitLayer F 5 :=
  gatesToLayer F (mulPassGates out left right passthroughs)

-- ============================================================
-- Section 3: Helpers
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
-- Section 4: Gate membership and matching helpers
-- ============================================================

theorem mem_mulPassGates_iff {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)} {gate : Gate 5} :
    gate ∈ mulPassGates out left right passthroughs ↔
    gate = ⟨.mul, out, left, right⟩ ∨
    ∃ p ∈ passthroughs, gate = ⟨.add, p, p, W_ZERO⟩ := by
  simp [mulPassGates, List.mem_cons, List.mem_map]
  constructor
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · left; rfl
    · right; exact ⟨p, hp, rfl⟩
  · rintro (rfl | ⟨p, hp, rfl⟩)
    · left; rfl
    · right; exact ⟨p, hp, rfl⟩

/-- No gate in `mulPassGates` has gate type `.add` with a given output position. -/
private theorem no_add_match {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)}
    (hpass_ne : ∀ p ∈ passthroughs, p ≠ out)
    (g l r : Fin 5 → Bool) (hg : g = out) :
    (mulPassGates out left right passthroughs).any
      (fun gate => gate.matches .add g l r) = false := by
  rw [List.any_eq_false]
  intro gate hmem
  rw [mem_mulPassGates_iff] at hmem
  rcases hmem with rfl | ⟨p, hp, rfl⟩
  · intro h; rw [Gate.matches_iff] at h; exact absurd h.1 GateType.noConfusion
  · intro h; rw [Gate.matches_iff] at h; exact hpass_ne p hp (h.2.1.trans hg)

/-- No gate in `mulPassGates` has gate type `.mul` with output different from `out`. -/
private theorem no_mul_match {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)}
    (g l r : Fin 5 → Bool) (hg : g ≠ out) :
    (mulPassGates out left right passthroughs).any
      (fun gate => gate.matches .mul g l r) = false := by
  rw [List.any_eq_false]
  intro gate hmem
  rw [mem_mulPassGates_iff] at hmem
  rcases hmem with rfl | ⟨_, _, rfl⟩
  · intro h; rw [Gate.matches_iff] at h; exact hg h.2.1.symm
  · intro h; rw [Gate.matches_iff] at h; exact absurd h.1 GateType.noConfusion

/-- No gate has output W_ZERO. -/
private theorem no_match_at_zero {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)}
    (hout_ne_zero : out ≠ W_ZERO)
    (hpass_ne_zero : ∀ p ∈ passthroughs, p ≠ W_ZERO)
    (ty : GateType) (l r : Fin 5 → Bool) :
    (mulPassGates out left right passthroughs).any
      (fun gate => gate.matches ty W_ZERO l r) = false := by
  rw [List.any_eq_false]
  intro gate hmem
  rw [mem_mulPassGates_iff] at hmem
  rcases hmem with rfl | ⟨p, hp, rfl⟩
  · intro h; rw [Gate.matches_iff] at h; exact hout_ne_zero h.2.1
  · intro h; rw [Gate.matches_iff] at h; exact hpass_ne_zero p hp h.2.1

/-- No gate in `mulPassGates` matches at an uncovered position. -/
private theorem no_match_uncovered {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)}
    (q : Fin 5 → Bool) (hq_ne_out : q ≠ out)
    (hq_not_pass : q ∉ passthroughs)
    (ty : GateType) (l r : Fin 5 → Bool) :
    (mulPassGates out left right passthroughs).any
      (fun gate => gate.matches ty q l r) = false := by
  rw [List.any_eq_false]
  intro gate hmem
  rw [mem_mulPassGates_iff] at hmem
  rcases hmem with rfl | ⟨p, hp, rfl⟩
  · intro h; rw [Gate.matches_iff] at h
    cases ty with
    | mul => exact hq_ne_out h.2.1.symm
    | add => exact absurd h.1 GateType.noConfusion
  · intro h; rw [Gate.matches_iff] at h
    cases ty with
    | add => exact hq_not_pass (h.2.1 ▸ hp)
    | mul => exact absurd h.1 GateType.noConfusion

/-- The passthrough gate list has at most one gate per output position. -/
private theorem passthrough_filter_le_one
    (ps : List (Fin 5 → Bool)) (hnodup : ps.Nodup) (g' : Fin 5 → Bool) :
    ((ps.map (fun p => (⟨GateType.add, p, p, W_ZERO⟩ : Gate 5))).filter
      (fun gate => decide (gate.output = g'))).length ≤ 1 := by
  induction ps with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [List.nodup_cons] at hnodup
    split
    · rename_i hhd_eq
      simp only [decide_eq_true_eq] at hhd_eq
      have : (tl.map (fun p => (⟨GateType.add, p, p, W_ZERO⟩ : Gate 5))).filter
          (fun gate => decide (gate.output = g')) = [] := by
        rw [List.filter_eq_nil_iff]
        intro gate hmem
        simp only [List.mem_map] at hmem
        obtain ⟨p, hp_tl, rfl⟩ := hmem
        simp only [decide_eq_true_eq]
        intro heq; exact hnodup.1 (hhd_eq ▸ heq ▸ hp_tl)
      rw [this]; simp
    · exact ih hnodup.2

/-- Each output position in mulPassGates has at most one gate. -/
private theorem mulPassGates_output_unique
    {out left right : Fin 5 → Bool}
    {passthroughs : List (Fin 5 → Bool)}
    (hpass_ne_out : ∀ p ∈ passthroughs, p ≠ out)
    (hpass_nodup : passthroughs.Nodup)
    (g' : Fin 5 → Bool) :
    ((mulPassGates out left right passthroughs).filter
      (fun gate => decide (gate.output = g'))).length ≤ 1 := by
  unfold mulPassGates
  simp only [List.filter_cons]
  split
  · rename_i hg'_out
    simp only [decide_eq_true_eq] at hg'_out
    have htail : (passthroughs.map (fun p => (⟨GateType.add, p, p, W_ZERO⟩ : Gate 5))).filter
        (fun gate => decide (gate.output = g')) = [] := by
      rw [List.filter_eq_nil_iff]
      intro gate hmem
      simp only [List.mem_map] at hmem
      obtain ⟨p, hp, rfl⟩ := hmem
      simp only [decide_eq_true_eq]
      intro heq; exact hpass_ne_out p hp (heq.trans hg'_out.symm)
    rw [htail]; simp
  · exact passthrough_filter_le_one passthroughs hpass_nodup g'

-- ============================================================
-- Section 5: mulPassLayer_iff — the key theorem
-- ============================================================

/-- Bidirectional semantics for `mulPassLayer`:
    Layer consistency at all positions iff the mul equation holds at `out`,
    pass-through equations hold, W_ZERO is zero, and all other positions are zero. -/
theorem mulPassLayer_iff
    (out left right : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool))
    (V_curr V_next : LayerValues F 5)
    (hout_ne_zero : out ≠ W_ZERO)
    (hpass_ne_zero : ∀ p ∈ passthroughs, p ≠ W_ZERO)
    (hpass_ne_out : ∀ p ∈ passthroughs, p ≠ out)
    (hpass_nodup : passthroughs.Nodup) :
    (∀ g, layerConsistent (mulPassLayer F out left right passthroughs) V_curr V_next g) ↔
    (V_curr.table out = V_next.table left * V_next.table right ∧
     (∀ p ∈ passthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ out → q ∉ passthroughs → q ≠ W_ZERO → V_curr.table q = 0)) := by
  constructor
  · -- Forward direction: extract equations from layerConsistent
    intro hall
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Mul equation at `out`
      have hg := hall out
      unfold layerConsistent mulPassLayer gatesToLayer at hg
      simp only [splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      -- Simplify the add part: no add gate matches at output=out
      have hadd_rw : ∀ l' r', (mulPassGates out left right passthroughs).any
          (fun gate => gate.matches .add out l' r') = false :=
        fun l' r' => @no_add_match out left right passthroughs hpass_ne_out out l' r' rfl
      simp_rw [hadd_rw]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, zero_add]
      -- Isolate the buildLR left right term
      rw [Finset.sum_eq_single (buildLR left right)]
      · simp only [splitL_buildLR, splitR_buildLR]
        have hmul : (mulPassGates out left right passthroughs).any
            (fun gate => gate.matches .mul out left right) = true := by
          rw [List.any_eq_true]
          exact ⟨⟨.mul, out, left, right⟩, List.mem_cons_self ..,
                 by rw [Gate.matches_iff]; exact ⟨rfl, rfl, rfl, rfl⟩⟩
        simp [hmul]
      · intro lr _ hlr
        have hlr' : splitL lr ≠ left ∨ splitR lr ≠ right := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hmul : (mulPassGates out left right passthroughs).any
            (fun gate => gate.matches .mul out (splitL lr) (splitR lr)) = false := by
          rw [List.any_eq_false]
          intro gate hmem; rw [mem_mulPassGates_iff] at hmem
          rcases hmem with rfl | ⟨_, _, rfl⟩
          · intro h; rw [Gate.matches_iff] at h
            rcases hlr' with hl | hr
            · exact hl h.2.2.1.symm
            · exact hr h.2.2.2.symm
          · intro h; rw [Gate.matches_iff] at h; exact absurd h.1 GateType.noConfusion
        simp [hmul]
      · simp
    · -- Pass-through equations
      intro p hp
      have hg := hall p
      unfold layerConsistent mulPassLayer gatesToLayer at hg
      simp only [splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      -- No mul gate matches at output=p (since p ≠ out)
      have hmul_rw : ∀ l' r', (mulPassGates out left right passthroughs).any
          (fun gate => gate.matches .mul p l' r') = false :=
        fun l' r' => @no_mul_match out left right passthroughs p l' r' (fun h => hpass_ne_out p hp h)
      simp_rw [hmul_rw]
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
      -- Isolate the buildLR p W_ZERO term
      rw [Finset.sum_eq_single (buildLR p W_ZERO)]
      · simp only [splitL_buildLR, splitR_buildLR]
        have hadd : (mulPassGates out left right passthroughs).any
            (fun gate => gate.matches .add p p W_ZERO) = true := by
          rw [List.any_eq_true]
          refine ⟨⟨.add, p, p, W_ZERO⟩, ?_, by rw [Gate.matches_iff]; exact ⟨rfl, rfl, rfl, rfl⟩⟩
          rw [mem_mulPassGates_iff]; right; exact ⟨p, hp, rfl⟩
        simp [hadd]
      · intro lr _ hlr
        have hlr' : splitL lr ≠ p ∨ splitR lr ≠ W_ZERO := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hadd : (mulPassGates out left right passthroughs).any
            (fun gate => gate.matches .add p (splitL lr) (splitR lr)) = false := by
          rw [List.any_eq_false]
          intro gate hmem; rw [mem_mulPassGates_iff] at hmem
          rcases hmem with rfl | ⟨p', _, rfl⟩
          · intro h; rw [Gate.matches_iff] at h; exact absurd h.1 GateType.noConfusion
          · intro h; rw [Gate.matches_iff] at h
            rcases hlr' with hl | hr
            · exact hl (h.2.2.1.symm.trans h.2.1)
            · exact hr h.2.2.2.symm
        simp [hadd]
      · simp
    · -- W_ZERO = 0
      have hg := hall W_ZERO
      unfold layerConsistent mulPassLayer gatesToLayer at hg
      simp only [splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      apply Finset.sum_eq_zero
      intro lr _
      have hadd := @no_match_at_zero out left right passthroughs hout_ne_zero hpass_ne_zero .add (splitL lr) (splitR lr)
      have hmul := @no_match_at_zero out left right passthroughs hout_ne_zero hpass_ne_zero .mul (splitL lr) (splitR lr)
      simp [hadd, hmul]
    · -- All other positions are zero
      intro q hq_ne_out hq_not_pass hq_ne_zero
      have hg := hall q
      unfold layerConsistent mulPassLayer gatesToLayer at hg
      simp only [splitG_concat3, splitLG_concat3, splitRG_concat3] at hg
      rw [hg]; clear hg
      apply Finset.sum_eq_zero
      intro lr _
      have hadd := @no_match_uncovered out left right passthroughs q hq_ne_out hq_not_pass .add (splitL lr) (splitR lr)
      have hmul := @no_match_uncovered out left right passthroughs q hq_ne_out hq_not_pass .mul (splitL lr) (splitR lr)
      simp [hadd, hmul]
  · -- Backward direction: use gatesToLayer_consistent
    intro ⟨hmul_eq, hpass_eq, hzero_eq, hcov⟩ g
    unfold mulPassLayer
    apply gatesToLayer_consistent
    · -- heval: each gate is correctly evaluated
      intro gate hmem
      rw [mem_mulPassGates_iff] at hmem
      rcases hmem with rfl | ⟨p, hp, rfl⟩
      · exact hmul_eq
      · exact hpass_eq p hp
    · -- huniq: each output position has at most one gate
      exact mulPassGates_output_unique hpass_ne_out hpass_nodup
    · -- hcovered: uncovered positions have value 0
      intro g' hg'
      -- hg' : ¬ (mulPassGates ...).any (fun gate => decide (gate.output = g')) = true
      -- We need to show V_curr.table g' = 0
      -- Extract: g' ≠ out
      have hg'_ne_out : g' ≠ out := by
        intro heq
        apply hg'; rw [heq]
        rw [List.any_eq_true]
        exact ⟨⟨.mul, out, left, right⟩, List.mem_cons_self ..,
               by simp⟩
      -- Extract: g' ∉ passthroughs
      have hg'_not_pass : g' ∉ passthroughs := by
        intro hmem; apply hg'
        rw [List.any_eq_true]
        refine ⟨⟨.add, g', g', W_ZERO⟩, ?_, by simp⟩
        rw [mem_mulPassGates_iff]; right; exact ⟨g', hmem, rfl⟩
      by_cases hg'_zero : g' = W_ZERO
      · rw [hg'_zero]; exact hzero_eq
      · exact hcov g' hg'_ne_out hg'_not_pass hg'_zero

-- ============================================================
-- Section 6: Zero-wire lemma
-- ============================================================

/-- In any `mulPassLayer`, the W_ZERO wire always evaluates to 0. -/
theorem zero_wire_uncovered_layer
    (out left right : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool))
    (hout_ne_zero : out ≠ W_ZERO)
    (hpass_ne_zero : ∀ p ∈ passthroughs, p ≠ W_ZERO)
    (hpass_ne_out : ∀ p ∈ passthroughs, p ≠ out)
    (hpass_nodup : passthroughs.Nodup)
    (V_curr V_next : LayerValues F 5)
    (hcons : ∀ g, layerConsistent (mulPassLayer F out left right passthroughs) V_curr V_next g) :
    V_curr.table W_ZERO = 0 :=
  ((mulPassLayer_iff F out left right passthroughs V_curr V_next
    hout_ne_zero hpass_ne_zero hpass_ne_out hpass_nodup).mp hcons).2.2.1

-- ============================================================
-- Section 7: Pass-through simplification
-- ============================================================

/-- If a pass-through equation holds and the zero wire is actually zero,
    then the wire value is preserved exactly between layers. -/
theorem passthrough_exact {F : Type*} [Field F] {p : Fin 5 → Bool}
    {V_curr V_next : LayerValues F 5}
    (hpass : V_curr.table p = V_next.table p + V_next.table W_ZERO)
    (hzero : V_next.table W_ZERO = 0) :
    V_curr.table p = V_next.table p := by
  rw [hpass, hzero, add_zero]

-- ============================================================
-- Section 8: coeffLayer — a layer with one coefficient-valued add gate
-- ============================================================

/-- A layer with one coefficient-valued add gate: `output = coeff * (V_next(src) + V_next(W_ZERO))`.

    Unlike `mulPassLayer` which uses `gatesToLayer` (producing 0/1 polynomials),
    `coeffLayer` directly constructs `add_poly` with an arbitrary field element `coeff`
    at position `(out, src, W_ZERO)`.  Pass-through positions have coefficient `1`.
    All other positions have coefficient `0`.  `mul_poly` is identically `0`.

    This enables encoding public inputs (e.g., `sig.s`, `z`, `sig.r`) into the
    layer structure itself, so that the circuit topology depends on the ECDSA instance. -/
noncomputable def coeffLayer (coeff : F) (out src : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool)) : CircuitLayer F 5 where
  add_poly := ⟨fun glr =>
    if glr = concat3 out src W_ZERO then coeff
    else if passthroughs.any (fun p => decide (glr = concat3 p p W_ZERO)) then 1
    else 0⟩
  mul_poly := ⟨fun _ => 0⟩

-- ============================================================
-- Section 8a: coeffLayer — helper to extract g component from concat3 equality
-- ============================================================

/-- If `concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂` then `g₁ = g₂`. -/
private theorem concat3_g_eq {s : ℕ} {g₁ g₂ l₁ l₂ r₁ r₂ : Fin s → Bool}
    (h : concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂) : g₁ = g₂ := by
  funext j; have := congrFun h ⟨j.val, by omega⟩; simp [concat3, j.isLt] at this; exact this

/-- If `concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂` then `l₁ = l₂`. -/
private theorem concat3_l_eq {s : ℕ} {g₁ g₂ l₁ l₂ r₁ r₂ : Fin s → Bool}
    (h : concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂) : l₁ = l₂ := by
  funext j
  have := congrFun h ⟨j.val + s, by omega⟩
  simp [concat3, show ¬(j.val + s < s) from by omega, show j.val + s < 2 * s from by omega] at this
  exact this

/-- If `concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂` then `r₁ = r₂`. -/
private theorem concat3_r_eq {s : ℕ} {g₁ g₂ l₁ l₂ r₁ r₂ : Fin s → Bool}
    (h : concat3 g₁ l₁ r₁ = concat3 g₂ l₂ r₂) : r₁ = r₂ := by
  funext j
  have := congrFun h ⟨j.val + 2 * s, by omega⟩
  simp [concat3, show ¬(j.val + 2 * s < s) from by omega,
        show ¬(j.val + 2 * s < 2 * s) from by omega] at this
  exact this

/-- The main triple doesn't match at a different gate output position. -/
private theorem coeffLayer_main_ne
    (out src q : Fin 5 → Bool) (hq_ne_out : q ≠ out)
    (l r : Fin 5 → Bool) :
    concat3 q l r ≠ concat3 out src W_ZERO := by
  intro heq; exact hq_ne_out (concat3_g_eq heq)

/-- `concat3 g l r ≠ concat3 g src W_ZERO` when `l ≠ src` or `r ≠ W_ZERO`. -/
private theorem concat3_ne_of_lr_ne
    (g src : Fin 5 → Bool) (l r : Fin 5 → Bool)
    (hlr : l ≠ src ∨ r ≠ W_ZERO) :
    concat3 g l r ≠ concat3 g src W_ZERO := by
  intro heq
  rcases hlr with hl | hr
  · exact hl (concat3_l_eq heq)
  · exact hr (concat3_r_eq heq)

-- ============================================================
-- Section 8b: coeffLayer — passthrough matching helpers
-- ============================================================

/-- No passthrough matches at the output position. -/
private theorem coeffLayer_no_pass_at_out
    (out _src : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool))
    (hpass_ne_out : ∀ p ∈ passthroughs, p ≠ out)
    (l r : Fin 5 → Bool) :
    passthroughs.any (fun p => decide (concat3 out l r = concat3 p p W_ZERO)) = false := by
  rw [List.any_eq_false]; intro p hp
  simp only [decide_eq_true_eq]; intro heq
  exact hpass_ne_out p hp (concat3_g_eq heq).symm

/-- No passthrough matches at W_ZERO position. -/
private theorem coeffLayer_no_pass_at_zero
    (passthroughs : List (Fin 5 → Bool))
    (hpass_ne_zero : ∀ p ∈ passthroughs, p ≠ W_ZERO)
    (l r : Fin 5 → Bool) :
    passthroughs.any (fun p => decide (concat3 W_ZERO l r = concat3 p p W_ZERO)) = false := by
  rw [List.any_eq_false]; intro p hp
  simp only [decide_eq_true_eq]; intro heq
  exact hpass_ne_zero p hp (concat3_g_eq heq).symm

/-- No passthrough matches at an uncovered position. -/
private theorem coeffLayer_no_pass_at_uncovered
    (q : Fin 5 → Bool) (passthroughs : List (Fin 5 → Bool))
    (hq_not_pass : q ∉ passthroughs)
    (l r : Fin 5 → Bool) :
    passthroughs.any (fun p => decide (concat3 q l r = concat3 p p W_ZERO)) = false := by
  rw [List.any_eq_false]; intro p hp
  simp only [decide_eq_true_eq]; intro heq
  exact hq_not_pass ((concat3_g_eq heq) ▸ hp)

/-- A passthrough matches at its own position. -/
private theorem coeffLayer_pass_self_match
    (passthroughs : List (Fin 5 → Bool))
    (p : Fin 5 → Bool) (hp : p ∈ passthroughs) :
    passthroughs.any (fun p' => decide (concat3 p p W_ZERO = concat3 p' p' W_ZERO)) = true := by
  rw [List.any_eq_true]; exact ⟨p, hp, by simp⟩

/-- No passthrough matches when splitL/splitR don't match any passthrough's (p, W_ZERO). -/
private theorem coeffLayer_no_pass_off_diag
    (g : Fin 5 → Bool) (passthroughs : List (Fin 5 → Bool))
    (_hnodup : passthroughs.Nodup)
    (lr : Fin (2 * 5) → Bool)
    (hlr : splitL lr ≠ g ∨ splitR lr ≠ W_ZERO)
    (_hg_pass : g ∈ passthroughs) :
    passthroughs.any (fun p' => decide (concat3 g (splitL lr) (splitR lr) = concat3 p' p' W_ZERO)) = false := by
  rw [List.any_eq_false]; intro p' hp'
  simp only [decide_eq_true_eq]; intro heq
  rcases hlr with hl | hr
  · exact hl ((concat3_g_eq heq).symm ▸ concat3_l_eq heq)
  · exact hr (concat3_r_eq heq)

-- ============================================================
-- Section 8c: coeffLayer_iff — bidirectional semantics
-- ============================================================

/-- Bidirectional semantics for `coeffLayer`:
    Layer consistency at all positions iff the coefficient equation holds at `out`,
    pass-through equations hold, W_ZERO is zero, and all other positions are zero. -/
theorem coeffLayer_iff
    (coeff : F) (out src : Fin 5 → Bool)
    (passthroughs : List (Fin 5 → Bool))
    (V_curr V_next : LayerValues F 5)
    (hout_ne_zero : out ≠ W_ZERO)
    (hpass_ne_zero : ∀ p ∈ passthroughs, p ≠ W_ZERO)
    (hpass_ne_out : ∀ p ∈ passthroughs, p ≠ out)
    (hpass_nodup : passthroughs.Nodup) :
    (∀ g, layerConsistent (coeffLayer F coeff out src passthroughs) V_curr V_next g) ↔
    (V_curr.table out = coeff * (V_next.table src + V_next.table W_ZERO) ∧
     (∀ p ∈ passthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO) ∧
     V_curr.table W_ZERO = 0 ∧
     (∀ q, q ≠ out → q ∉ passthroughs → q ≠ W_ZERO → V_curr.table q = 0)) := by
  constructor
  · -- Forward direction: extract equations from layerConsistent
    intro hall
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Coefficient equation at `out`
      have hg := hall out
      unfold layerConsistent coeffLayer at hg
      simp only at hg; rw [hg]; clear hg
      rw [Finset.sum_eq_single (buildLR src W_ZERO)]
      · simp only [splitL_buildLR, splitR_buildLR]; simp
      · intro lr _ hlr
        have hlr' : splitL lr ≠ src ∨ splitR lr ≠ W_ZERO := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hne := concat3_ne_of_lr_ne out src (splitL lr) (splitR lr) hlr'
        have hno_pass := coeffLayer_no_pass_at_out out src passthroughs hpass_ne_out (splitL lr) (splitR lr)
        simp [hne, hno_pass]
      · simp
    · -- Pass-through equations
      intro p hp
      have hg := hall p
      unfold layerConsistent coeffLayer at hg
      simp only at hg; rw [hg]; clear hg
      rw [Finset.sum_eq_single (buildLR p W_ZERO)]
      · simp only [splitL_buildLR, splitR_buildLR]
        have hne_main := coeffLayer_main_ne out src p (hpass_ne_out p hp) p W_ZERO
        have hpass_match := coeffLayer_pass_self_match passthroughs p hp
        simp [hne_main, hpass_match]
      · intro lr _ hlr
        have hlr' : splitL lr ≠ p ∨ splitR lr ≠ W_ZERO := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hne_main := coeffLayer_main_ne out src p (hpass_ne_out p hp) (splitL lr) (splitR lr)
        have hno_pass := coeffLayer_no_pass_off_diag p passthroughs hpass_nodup lr hlr' hp
        simp [hne_main, hno_pass]
      · simp
    · -- W_ZERO = 0
      have hg := hall W_ZERO
      unfold layerConsistent coeffLayer at hg
      simp only at hg; rw [hg]; clear hg
      apply Finset.sum_eq_zero; intro lr _
      have hne_main := coeffLayer_main_ne out src W_ZERO hout_ne_zero.symm (splitL lr) (splitR lr)
      have hno_pass := coeffLayer_no_pass_at_zero passthroughs hpass_ne_zero (splitL lr) (splitR lr)
      simp [hne_main, hno_pass]
    · -- All other positions are zero
      intro q hq_ne_out hq_not_pass hq_ne_zero
      have hg := hall q
      unfold layerConsistent coeffLayer at hg
      simp only at hg; rw [hg]; clear hg
      apply Finset.sum_eq_zero; intro lr _
      have hne_main := coeffLayer_main_ne out src q hq_ne_out (splitL lr) (splitR lr)
      have hno_pass := coeffLayer_no_pass_at_uncovered q passthroughs hq_not_pass (splitL lr) (splitR lr)
      simp [hne_main, hno_pass]
  · -- Backward direction: construct layerConsistent from equations
    intro ⟨hcoeff_eq, hpass_eq, hzero_eq, hcov⟩ g
    unfold layerConsistent coeffLayer; simp only
    by_cases hg_out : g = out
    · -- g = out
      subst hg_out; rw [hcoeff_eq]
      rw [Finset.sum_eq_single (buildLR src W_ZERO)]
      · simp only [splitL_buildLR, splitR_buildLR]; simp
      · intro lr _ hlr
        have hlr' : splitL lr ≠ src ∨ splitR lr ≠ W_ZERO := by
          by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
        have hne := concat3_ne_of_lr_ne g src (splitL lr) (splitR lr) hlr'
        have hno_pass := coeffLayer_no_pass_at_out g src passthroughs hpass_ne_out (splitL lr) (splitR lr)
        simp [hne, hno_pass]
      · simp
    · by_cases hg_pass : g ∈ passthroughs
      · -- g ∈ passthroughs
        rw [hpass_eq g hg_pass]
        rw [Finset.sum_eq_single (buildLR g W_ZERO)]
        · simp only [splitL_buildLR, splitR_buildLR]
          have hne_main := coeffLayer_main_ne out src g hg_out g W_ZERO
          have hpass_match := coeffLayer_pass_self_match passthroughs g hg_pass
          simp [hne_main, hpass_match]
        · intro lr _ hlr
          have hlr' : splitL lr ≠ g ∨ splitR lr ≠ W_ZERO := by
            by_contra h; push Not at h; exact hlr (buildLR_unique h.1 h.2)
          have hne_main := coeffLayer_main_ne out src g hg_out (splitL lr) (splitR lr)
          have hno_pass := coeffLayer_no_pass_off_diag g passthroughs hpass_nodup lr hlr' hg_pass
          simp [hne_main, hno_pass]
        · simp
      · by_cases hg_zero : g = W_ZERO
        · -- g = W_ZERO
          subst hg_zero; rw [hzero_eq]; symm
          apply Finset.sum_eq_zero; intro lr _
          have hne_main := coeffLayer_main_ne out src W_ZERO hg_out (splitL lr) (splitR lr)
          have hno_pass := coeffLayer_no_pass_at_zero passthroughs hpass_ne_zero (splitL lr) (splitR lr)
          simp [hne_main, hno_pass]
        · -- uncovered
          rw [hcov g hg_out hg_pass hg_zero]; symm
          apply Finset.sum_eq_zero; intro lr _
          have hne_main := coeffLayer_main_ne out src g hg_out (splitL lr) (splitR lr)
          have hno_pass := coeffLayer_no_pass_at_uncovered g passthroughs hg_pass (splitL lr) (splitR lr)
          simp [hne_main, hno_pass]
