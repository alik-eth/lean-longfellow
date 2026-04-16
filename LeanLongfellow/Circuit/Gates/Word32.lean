import LeanLongfellow.Circuit.Gadgets

open Finset

/-! # Word32 Arithmetic Gadgets for SHA-256 Circuit Verification

32-bit words are `Fin 32 → F` with boolean entries.
Operations are compositions of gadgets from `Gadgets.lean`.
-/

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Representation
-- ============================================================

/-- All entries of a 32-bit word are boolean. -/
def isWord32 (bits : Fin 32 → F) : Prop := ∀ i, isBool (bits i)

/-- The value of a 32-bit word as a field element: ∑ bits(i) * 2^i. -/
def word32Val (bits : Fin 32 → F) : F := ∑ i : Fin 32, bits i * (2 : F) ^ (i : ℕ)

-- ============================================================
-- Section 2: NOT — complement each bit
-- ============================================================

/-- Bitwise NOT: complement each bit. -/
def word32Not (a : Fin 32 → F) : Fin 32 → F := fun i => 1 - a i

theorem word32Not_bool (a : Fin 32 → F) (ha : isWord32 a) :
    isWord32 (word32Not a) := by
  intro i
  unfold word32Not isBool
  rcases (isBool_iff (a i)).mp (ha i) with h | h <;> rw [h] <;> ring

-- ============================================================
-- Section 3: AND — pointwise multiplication
-- ============================================================

/-- Bitwise AND: pointwise multiplication. -/
def word32And (a b : Fin 32 → F) : Fin 32 → F := fun i => a i * b i

theorem word32And_bool (a b : Fin 32 → F) (ha : isWord32 a) (hb : isWord32 b) :
    isWord32 (word32And a b) := by
  intro i
  unfold word32And isBool
  rcases (isBool_iff (a i)).mp (ha i) with h | h <;>
    rcases (isBool_iff (b i)).mp (hb i) with h' | h' <;>
    rw [h, h'] <;> ring

-- ============================================================
-- Section 4: XOR — a + b - 2*a*b
-- ============================================================

/-- Bitwise XOR: a + b - 2*a*b. -/
def word32Xor (a b : Fin 32 → F) : Fin 32 → F := fun i => a i + b i - 2 * a i * b i

theorem word32Xor_bool (a b : Fin 32 → F) (ha : isWord32 a) (hb : isWord32 b) :
    isWord32 (word32Xor a b) := by
  intro i
  unfold word32Xor isBool
  rcases (isBool_iff (a i)).mp (ha i) with h | h <;>
    rcases (isBool_iff (b i)).mp (hb i) with h' | h' <;>
    rw [h, h'] <;> ring

-- ============================================================
-- Section 5: RotR — right rotation by constant k
-- ============================================================

/-- Right rotation by k positions. -/
def word32RotR (a : Fin 32 → F) (k : ℕ) : Fin 32 → F :=
  fun i => a ⟨(i.val + k) % 32, Nat.mod_lt _ (by omega)⟩

theorem word32RotR_bool (a : Fin 32 → F) (ha : isWord32 a) (k : ℕ) :
    isWord32 (word32RotR a k) := by
  intro i; exact ha _

-- ============================================================
-- Section 6: ShR — right shift by constant k (zero-fill)
-- ============================================================

/-- Right shift by k positions, zero-filling high bits. -/
def word32ShR (a : Fin 32 → F) (k : ℕ) : Fin 32 → F :=
  fun i => if h : i.val + k < 32 then a ⟨i.val + k, h⟩ else 0

theorem word32ShR_bool (a : Fin 32 → F) (ha : isWord32 a) (k : ℕ) :
    isWord32 (word32ShR a k) := by
  intro i
  simp only [word32ShR]
  split
  · exact ha _
  · exact (isBool_iff _).mpr (Or.inl rfl)

-- ============================================================
-- Section 7: Add mod 2^32 — constraint relation
-- ============================================================

/-- Addition mod 2^32 as a constraint.
    The prover supplies result bits c and a carry bit;
    the verifier checks that a + b = c + carry * 2^32. -/
def word32Add (a b c : Fin 32 → F) (carry : F) : Prop :=
  isWord32 c ∧ isBool carry ∧
  word32Val a + word32Val b = word32Val c + carry * (2 : F) ^ 32

/-- The result of word32Add is a valid word. -/
theorem word32Add_result_bool (a b c : Fin 32 → F) (carry : F)
    (h : word32Add a b c carry) : isWord32 c := h.1

/-- The carry of word32Add is boolean. -/
theorem word32Add_carry_bool (a b c : Fin 32 → F) (carry : F)
    (h : word32Add a b c carry) : isBool carry := h.2.1

-- ============================================================
-- Section 8: Value-level correctness
-- ============================================================

/-- NOT value: word32Val(¬a) = (∑ 2^i) - word32Val(a) when a is a valid word. -/
theorem word32Not_val (a : Fin 32 → F) :
    word32Val (word32Not a) = (∑ i : Fin 32, (2 : F) ^ (i : ℕ)) - word32Val a := by
  simp only [word32Val, word32Not]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- XOR value: pointwise, each bit satisfies xor semantics. -/
theorem word32Xor_bit (a b : Fin 32 → F) (i : Fin 32) :
    word32Xor a b i = a i + b i - 2 * a i * b i := rfl

/-- AND value: pointwise, each bit is the product. -/
theorem word32And_bit (a b : Fin 32 → F) (i : Fin 32) :
    word32And a b i = a i * b i := rfl

omit [Field F] in
/-- RotR is an index permutation. -/
theorem word32RotR_bit (a : Fin 32 → F) (k : ℕ) (i : Fin 32) :
    word32RotR a k i = a ⟨(i.val + k) % 32, Nat.mod_lt _ (by omega)⟩ := rfl
