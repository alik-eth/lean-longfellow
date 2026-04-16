import LeanLongfellow.Circuit.Gates.Word32

open Finset

/-! # SHA-256 Round Function

Auxiliary functions (Ch, Maj, Σ0, Σ1, σ0, σ1) and one-round constraint
for SHA-256, built as compositions of Word32 gadgets.
-/

set_option autoImplicit false

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Auxiliary Bit-Functions
-- ============================================================

/-- Choice: Ch(e, f, g) = (e AND f) XOR (NOT e AND g). -/
def sha256Ch (e f g : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32And e f) (word32And (word32Not e) g)

/-- Majority: Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c). -/
def sha256Maj (a b c : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32Xor (word32And a b) (word32And a c)) (word32And b c)

/-- Big Sigma 0: Σ0(a) = RotR(a,2) XOR RotR(a,13) XOR RotR(a,22). -/
def sha256BigSigma0 (a : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32Xor (word32RotR a 2) (word32RotR a 13)) (word32RotR a 22)

/-- Big Sigma 1: Σ1(e) = RotR(e,6) XOR RotR(e,11) XOR RotR(e,25). -/
def sha256BigSigma1 (e : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32Xor (word32RotR e 6) (word32RotR e 11)) (word32RotR e 25)

/-- Small sigma 0: σ0(x) = RotR(x,7) XOR RotR(x,18) XOR ShR(x,3). -/
def sha256SmallSigma0 (x : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32Xor (word32RotR x 7) (word32RotR x 18)) (word32ShR x 3)

/-- Small sigma 1: σ1(x) = RotR(x,17) XOR RotR(x,19) XOR ShR(x,10). -/
def sha256SmallSigma1 (x : Fin 32 → F) : Fin 32 → F :=
  word32Xor (word32Xor (word32RotR x 17) (word32RotR x 19)) (word32ShR x 10)

-- ============================================================
-- Section 2: Boolean Preservation
-- ============================================================

theorem sha256Ch_bool (e f g : Fin 32 → F)
    (he : isWord32 e) (hf : isWord32 f) (hg : isWord32 g) :
    isWord32 (sha256Ch e f g) :=
  word32Xor_bool _ _ (word32And_bool _ _ he hf) (word32And_bool _ _ (word32Not_bool _ he) hg)

theorem sha256Maj_bool (a b c : Fin 32 → F)
    (ha : isWord32 a) (hb : isWord32 b) (hc : isWord32 c) :
    isWord32 (sha256Maj a b c) :=
  word32Xor_bool _ _
    (word32Xor_bool _ _ (word32And_bool _ _ ha hb) (word32And_bool _ _ ha hc))
    (word32And_bool _ _ hb hc)

theorem sha256BigSigma0_bool (a : Fin 32 → F) (ha : isWord32 a) :
    isWord32 (sha256BigSigma0 a) :=
  word32Xor_bool _ _
    (word32Xor_bool _ _ (word32RotR_bool _ ha 2) (word32RotR_bool _ ha 13))
    (word32RotR_bool _ ha 22)

theorem sha256BigSigma1_bool (e : Fin 32 → F) (he : isWord32 e) :
    isWord32 (sha256BigSigma1 e) :=
  word32Xor_bool _ _
    (word32Xor_bool _ _ (word32RotR_bool _ he 6) (word32RotR_bool _ he 11))
    (word32RotR_bool _ he 25)

theorem sha256SmallSigma0_bool (x : Fin 32 → F) (hx : isWord32 x) :
    isWord32 (sha256SmallSigma0 x) :=
  word32Xor_bool _ _
    (word32Xor_bool _ _ (word32RotR_bool _ hx 7) (word32RotR_bool _ hx 18))
    (word32ShR_bool _ hx 3)

theorem sha256SmallSigma1_bool (x : Fin 32 → F) (hx : isWord32 x) :
    isWord32 (sha256SmallSigma1 x) :=
  word32Xor_bool _ _
    (word32Xor_bool _ _ (word32RotR_bool _ hx 17) (word32RotR_bool _ hx 19))
    (word32ShR_bool _ hx 10)

-- ============================================================
-- Section 3: SHA-256 State & Round Constraint
-- ============================================================

/-- SHA-256 working state: 8 words (a, b, c, d, e, f, g, h). -/
structure SHA256State (F : Type*) [Field F] where
  a : Fin 32 → F
  b : Fin 32 → F
  c : Fin 32 → F
  d : Fin 32 → F
  e : Fin 32 → F
  f : Fin 32 → F
  g : Fin 32 → F
  h : Fin 32 → F

/-- All state words are valid 32-bit words. -/
def SHA256State.isValid (st : SHA256State F) : Prop :=
  isWord32 st.a ∧ isWord32 st.b ∧ isWord32 st.c ∧ isWord32 st.d ∧
  isWord32 st.e ∧ isWord32 st.f ∧ isWord32 st.g ∧ isWord32 st.h

/-- One SHA-256 round step as a constraint.

    `K_i` and `W_i` are the round constant and message schedule word.
    `t1` and `t2` are witness words for the two temporary values.
    Carries are existentially quantified inside the constraint so that
    the caller does not need to thread them.

    T1 = h + Σ1(e) + Ch(e,f,g) + K_i + W_i  (mod 2^32)
    T2 = Σ0(a) + Maj(a,b,c)                   (mod 2^32)

    New state:  a' = T1 + T2,  b' = a,  c' = b,  d' = c,
                e' = d + T1,   f' = e,  g' = f,  h' = g.  -/
def sha256RoundConstraint (st st' : SHA256State F) (K_i W_i : Fin 32 → F)
    (t1 t2 : Fin 32 → F) (carry_t2 carry_a carry_e : F) : Prop :=
  -- T1: five-operand sum mod 2^32; overflow can be 0..4
  isWord32 t1 ∧
  (∃ overflow : ℕ, overflow ≤ 4 ∧
    word32Val st.h + word32Val (sha256BigSigma1 st.e) +
      word32Val (sha256Ch st.e st.f st.g) + word32Val K_i + word32Val W_i =
      word32Val t1 + (overflow : F) * (2 : F) ^ 32) ∧
  -- T2 = Σ0(a) + Maj(a,b,c)  (mod 2^32)
  word32Add (sha256BigSigma0 st.a) (sha256Maj st.a st.b st.c) t2 carry_t2 ∧
  -- a' = T1 + T2  (mod 2^32)
  word32Add t1 t2 st'.a carry_a ∧
  -- e' = d + T1   (mod 2^32)
  word32Add st.d t1 st'.e carry_e ∧
  -- Simple assignments
  st'.b = st.a ∧ st'.c = st.b ∧ st'.d = st.c ∧
  st'.f = st.e ∧ st'.g = st.f ∧ st'.h = st.g

-- ============================================================
-- Section 4: Round Preserves Validity
-- ============================================================

/-- A valid round step preserves state validity. -/
theorem sha256RoundConstraint_valid (st st' : SHA256State F)
    (K_i W_i t1 t2 : Fin 32 → F)
    (carry_t2 carry_a carry_e : F)
    (hst : st.isValid) (_hK : isWord32 K_i) (_hW : isWord32 W_i)
    (hround : sha256RoundConstraint st st' K_i W_i t1 t2
      carry_t2 carry_a carry_e) :
    st'.isValid := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := hst
  obtain ⟨ht1_w, _, ht2_add, ha'_add, he'_add,
          hb'_eq, hc'_eq, hd'_eq, hf'_eq, hg'_eq, hh'_eq⟩ := hround
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha'_add.1           -- a' is word32 (from word32Add)
  · rw [hb'_eq]; exact ha     -- b' = a
  · rw [hc'_eq]; exact hb     -- c' = b
  · rw [hd'_eq]; exact hc     -- d' = c
  · exact he'_add.1           -- e' is word32 (from word32Add)
  · rw [hf'_eq]; exact he     -- f' = e
  · rw [hg'_eq]; exact hf     -- g' = f
  · rw [hh'_eq]; exact hg     -- h' = g
