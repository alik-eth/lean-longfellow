import LeanLongfellow.Circuit.Gates

set_option autoImplicit false

/-! # IETF §12 Wire Format Bridge

Connects the IETF Quad wire format (delta-encoded gate indices) to
our abstract `CircuitLayer` model via `Gate` and `gatesToLayer`.
-/

-- ============================================================
-- Section 1: IETF Quad types
-- ============================================================

/-- A raw IETF Quad entry (delta-encoded). -/
structure DeltaQuad where
  delta_g : Int
  delta_h0 : Int
  delta_h1 : Int
  v : ℕ

/-- An absolute-index Quad (after delta decoding). -/
structure AbsQuad where
  g : ℕ
  h0 : ℕ
  h1 : ℕ
  v : ℕ
  deriving DecidableEq, BEq

-- ============================================================
-- Section 2: Delta decoding / encoding
-- ============================================================

/-- Decode delta quads to absolute quads, given running absolute indices. -/
def decodeDeltaQuadsAux (pG pH0 pH1 : Int) : List DeltaQuad → List AbsQuad
  | [] => []
  | dq :: rest =>
    let absG := pG + dq.delta_g
    let absH0 := pH0 + dq.delta_h0
    let absH1 := pH1 + dq.delta_h1
    ⟨absG.toNat, absH0.toNat, absH1.toNat, dq.v⟩ :: decodeDeltaQuadsAux absG absH0 absH1 rest

/-- Decode a list of delta-encoded quads into absolute indices. -/
def decodeDeltaQuads (quads : List DeltaQuad) : List AbsQuad :=
  decodeDeltaQuadsAux 0 0 0 quads

/-- Encode absolute quads to delta form, given running absolute indices. -/
def encodeDeltaQuadsAux (pG pH0 pH1 : Int) : List AbsQuad → List DeltaQuad
  | [] => []
  | aq :: rest =>
    ⟨(aq.g : Int) - pG, (aq.h0 : Int) - pH0, (aq.h1 : Int) - pH1, aq.v⟩ ::
      encodeDeltaQuadsAux aq.g aq.h0 aq.h1 rest

/-- Encode absolute quads back to delta form. -/
def encodeDeltaQuads (quads : List AbsQuad) : List DeltaQuad :=
  encodeDeltaQuadsAux 0 0 0 quads

-- ============================================================
-- Section 3: Bit-vector conversion
-- ============================================================

/-- Convert a natural number to its s-bit binary representation. -/
def natToBoolVec (s : ℕ) (n : ℕ) : Fin s → Bool :=
  fun i => (n / 2 ^ i.val) % 2 = 1

@[simp] theorem natToBoolVec_zero (s : ℕ) : natToBoolVec s 0 = fun _ => false := by
  funext i; simp [natToBoolVec]

theorem natToBoolVec_injective (s : ℕ) (a b : ℕ) (ha : a < 2 ^ s) (hb : b < 2 ^ s)
    (h : natToBoolVec s a = natToBoolVec s b) : a = b := by
  induction s generalizing a b with
  | zero => omega
  | succ n ih =>
    have ha' : a / 2 < 2 ^ n := Nat.div_lt_of_lt_mul (by omega)
    have hb' : b / 2 < 2 ^ n := Nat.div_lt_of_lt_mul (by omega)
    have h0 : (a / 2 ^ 0) % 2 = (b / 2 ^ 0) % 2 := by
      have := congrFun h (⟨0, by omega⟩ : Fin (n + 1))
      simp [natToBoolVec] at this
      omega
    simp at h0
    have htail : natToBoolVec n (a / 2) = natToBoolVec n (b / 2) := by
      funext ⟨j, hj⟩
      have hbit := congrFun h (⟨j + 1, by omega⟩ : Fin (n + 1))
      simp only [natToBoolVec] at hbit ⊢
      simp_rw [Nat.div_div_eq_div_mul]
      have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      rwa [hpow] at hbit
    have hdiv := ih (a / 2) (b / 2) ha' hb' htail
    omega

-- ============================================================
-- Section 4: Quad to Gate conversion
-- ============================================================

/-- Convert an absolute-index quad to a `Gate`. -/
def absQuadToGate (s : ℕ) (q : AbsQuad) : Gate s where
  gateType := if q.v = 0 then .add else .mul
  output := natToBoolVec s q.g
  left := natToBoolVec s q.h0
  right := natToBoolVec s q.h1

theorem absQuadToGate_type (s : ℕ) (q : AbsQuad) :
    (absQuadToGate s q).gateType = if q.v = 0 then .add else .mul := by
  simp [absQuadToGate]

theorem absQuadToGate_output (s : ℕ) (q : AbsQuad) :
    (absQuadToGate s q).output = natToBoolVec s q.g := by
  simp [absQuadToGate]

-- ============================================================
-- Section 5: Full pipeline
-- ============================================================

/-- Full IETF pipeline: delta quads → absolute quads → gates → CircuitLayer. -/
noncomputable def ietfToCircuitLayer (F : Type*) [Field F] (s : ℕ)
    (quads : List DeltaQuad) : CircuitLayer F s :=
  gatesToLayer F (quads |> decodeDeltaQuads |>.map (absQuadToGate s))

-- ============================================================
-- Section 6: Round-trip property
-- ============================================================

private theorem decode_encode_aux (pG pH0 pH1 : Int) (quads : List AbsQuad) :
    decodeDeltaQuadsAux pG pH0 pH1 (encodeDeltaQuadsAux pG pH0 pH1 quads) = quads := by
  induction quads generalizing pG pH0 pH1 with
  | nil => simp [encodeDeltaQuadsAux, decodeDeltaQuadsAux]
  | cons q qs ih =>
    simp only [encodeDeltaQuadsAux, decodeDeltaQuadsAux]
    have hg : pG + (↑q.g - pG) = ↑q.g := by omega
    have hh0 : pH0 + (↑q.h0 - pH0) = ↑q.h0 := by omega
    have hh1 : pH1 + (↑q.h1 - pH1) = ↑q.h1 := by omega
    rw [hg, hh0, hh1]
    simp [Int.toNat_natCast, ih]

/-- Delta encoding then decoding is the identity. -/
theorem decode_encode_id (quads : List AbsQuad) :
    decodeDeltaQuads (encodeDeltaQuads quads) = quads :=
  decode_encode_aux 0 0 0 quads
