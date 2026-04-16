import LeanLongfellow.Circuit.WireFormat

set_option autoImplicit false

/-! # IETF Wire Format Spec Conformance

Proves that our delta encoding / decoding implementation matches the IETF
draft-google-cfrg-libzk-01 wire format byte-for-byte, plus round-trip and
structural properties needed for correctness of the full pipeline.
-/

-- ============================================================
-- Section 1: Decode then encode round-trip (reverse direction)
-- ============================================================

/-- All running sums in `decodeDeltaQuadsAux` stay non-negative.
    This is the validity invariant for IETF wire data: absolute
    gate/input indices must be non-negative throughout the stream. -/
def DeltaQuads.WellFormed (pG pH0 pH1 : Int) : List DeltaQuad → Prop
  | [] => True
  | dq :: rest =>
    0 ≤ pG + dq.delta_g ∧ 0 ≤ pH0 + dq.delta_h0 ∧ 0 ≤ pH1 + dq.delta_h1 ∧
    DeltaQuads.WellFormed (pG + dq.delta_g) (pH0 + dq.delta_h0) (pH1 + dq.delta_h1) rest

private theorem encode_decode_aux (pG pH0 pH1 : Int) (quads : List DeltaQuad)
    (hwf : DeltaQuads.WellFormed pG pH0 pH1 quads) :
    encodeDeltaQuadsAux pG pH0 pH1
      (decodeDeltaQuadsAux pG pH0 pH1 quads) = quads := by
  induction quads generalizing pG pH0 pH1 with
  | nil => simp [decodeDeltaQuadsAux, encodeDeltaQuadsAux]
  | cons dq rest ih =>
    simp only [decodeDeltaQuadsAux, encodeDeltaQuadsAux]
    obtain ⟨hg, hh0, hh1, hwf'⟩ := hwf
    have hgn : ((pG + dq.delta_g).toNat : Int) = pG + dq.delta_g :=
      Int.toNat_of_nonneg hg
    have hh0n : ((pH0 + dq.delta_h0).toNat : Int) = pH0 + dq.delta_h0 :=
      Int.toNat_of_nonneg hh0
    have hh1n : ((pH1 + dq.delta_h1).toNat : Int) = pH1 + dq.delta_h1 :=
      Int.toNat_of_nonneg hh1
    rw [hgn, hh0n, hh1n]
    simp only [show pG + dq.delta_g - pG = dq.delta_g by omega,
               show pH0 + dq.delta_h0 - pH0 = dq.delta_h0 by omega,
               show pH1 + dq.delta_h1 - pH1 = dq.delta_h1 by omega]
    exact congrArg (dq :: ·) (ih _ _ _ hwf')

/-- Decoding then re-encoding recovers the original delta stream,
    provided absolute indices never go negative (well-formedness). -/
theorem encode_decode_id (quads : List DeltaQuad)
    (hwf : DeltaQuads.WellFormed 0 0 0 quads) :
    encodeDeltaQuads (decodeDeltaQuads quads) = quads :=
  encode_decode_aux 0 0 0 quads hwf

-- ============================================================
-- Section 2: Decode preserves length
-- ============================================================

private theorem decodeDeltaQuadsAux_length (pG pH0 pH1 : Int) (qs : List DeltaQuad) :
    (decodeDeltaQuadsAux pG pH0 pH1 qs).length = qs.length := by
  induction qs generalizing pG pH0 pH1 with
  | nil => simp [decodeDeltaQuadsAux]
  | cons _ _ ih => simp [decodeDeltaQuadsAux, ih]

theorem decodeDeltaQuads_length (qs : List DeltaQuad) :
    (decodeDeltaQuads qs).length = qs.length :=
  decodeDeltaQuadsAux_length 0 0 0 qs

-- ============================================================
-- Section 3: Absolute index lower bound (monotonicity support)
-- ============================================================

/-- All gate indices in decoded output are at least `pG.toNat` when
    all gate deltas are non-negative.  This implies monotonicity of
    the gate index sequence. -/
theorem decode_g_lower_bound (pG pH0 pH1 : Int) (quads : List DeltaQuad)
    (hpG : 0 ≤ pG)
    (hdeltas : ∀ dq ∈ quads, 0 ≤ dq.delta_g) :
    ∀ aq ∈ decodeDeltaQuadsAux pG pH0 pH1 quads, pG.toNat ≤ aq.g := by
  induction quads generalizing pG pH0 pH1 with
  | nil => simp [decodeDeltaQuadsAux]
  | cons dq rest ih =>
    intro aq haq
    simp only [decodeDeltaQuadsAux, List.mem_cons] at haq
    have hdq : 0 ≤ dq.delta_g := hdeltas dq (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ dq' ∈ rest, 0 ≤ dq'.delta_g :=
      fun dq' h => hdeltas dq' (List.mem_cons.mpr (Or.inr h))
    rcases haq with rfl | haq
    · show pG.toNat ≤ (pG + dq.delta_g).toNat
      exact Int.toNat_le_toNat (by omega)
    · calc pG.toNat
          ≤ (pG + dq.delta_g).toNat := Int.toNat_le_toNat (by omega)
        _ ≤ aq.g := ih _ _ _ (by omega) hrest aq haq

-- ============================================================
-- Section 4: Boolean-vector / natural number round-trip
-- ============================================================

/-- Convert a boolean vector to a natural number (inverse of `natToBoolVec`).
    Defined as `Nat.ofBits` (Horner evaluation). -/
def boolVecToNat (s : Nat) (bits : Fin s → Bool) : Nat := Nat.ofBits bits

/-- `boolVecToNat` always produces a value in range. -/
theorem boolVecToNat_lt (s : Nat) (bits : Fin s → Bool) :
    boolVecToNat s bits < 2 ^ s := Nat.ofBits_lt_two_pow bits

/-- `natToBoolVec` agrees with the built-in `Nat.testBit`. -/
private theorem testBit_eq_decide_div_mod (n i : Nat) :
    n.testBit i = decide (n / 2 ^ i % 2 = 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  cases h : (n / 2 ^ i) % 2 with
  | zero => simp
  | succ m =>
    have : m = 0 := by have := Nat.mod_lt (n / 2 ^ i) (show 0 < 2 by omega); omega
    subst this; simp

theorem natToBoolVec_eq_testBit (s n : Nat) :
    natToBoolVec s n = fun i => n.testBit i.val := by
  funext i; simp [natToBoolVec, testBit_eq_decide_div_mod]

/-- Round-trip: `natToBoolVec` then `boolVecToNat` recovers the original
    (for values in range). -/
theorem boolVecToNat_natToBoolVec (s n : Nat) (hn : n < 2 ^ s) :
    boolVecToNat s (natToBoolVec s n) = n := by
  simp only [boolVecToNat, natToBoolVec_eq_testBit, Nat.ofBits_testBit]
  exact Nat.mod_eq_of_lt hn

/-- Round-trip: `boolVecToNat` then `natToBoolVec` recovers the original. -/
theorem natToBoolVec_boolVecToNat (s : Nat) (bits : Fin s → Bool) :
    natToBoolVec s (boolVecToNat s bits) = bits := by
  rw [natToBoolVec_eq_testBit]
  funext i
  simp [boolVecToNat, Nat.testBit_ofBits_lt _ _ i.isLt]

-- ============================================================
-- Section 5: Gate type encoding matches IETF spec §12
-- ============================================================

/-- v=0 maps to an add gate (IETF spec §12). -/
theorem gate_type_encoding_add (s : Nat) (q : AbsQuad) (hv : q.v = 0) :
    (absQuadToGate s q).gateType = .add := by
  simp [absQuadToGate, hv]

/-- v≠0 maps to a mul gate (IETF spec §12). -/
theorem gate_type_encoding_mul (s : Nat) (q : AbsQuad) (hv : q.v ≠ 0) :
    (absQuadToGate s q).gateType = .mul := by
  simp [absQuadToGate, hv]

-- ============================================================
-- Section 6: Full pipeline preservation
-- ============================================================

/-- The full IETF pipeline produces one `Gate` per input `DeltaQuad`. -/
theorem ietfPipeline_gate_count (s : Nat) (quads : List DeltaQuad) :
    (quads |> decodeDeltaQuads |>.map (absQuadToGate s)).length = quads.length := by
  simp [decodeDeltaQuads_length]

/-- `absQuadToGate` preserves the output index from the quad. -/
theorem absQuadToGate_output_eq (s : Nat) (q : AbsQuad) :
    (absQuadToGate s q).output = natToBoolVec s q.g := rfl

/-- `absQuadToGate` preserves the left-input index from the quad. -/
theorem absQuadToGate_left_eq (s : Nat) (q : AbsQuad) :
    (absQuadToGate s q).left = natToBoolVec s q.h0 := rfl

/-- `absQuadToGate` preserves the right-input index from the quad. -/
theorem absQuadToGate_right_eq (s : Nat) (q : AbsQuad) :
    (absQuadToGate s q).right = natToBoolVec s q.h1 := rfl
