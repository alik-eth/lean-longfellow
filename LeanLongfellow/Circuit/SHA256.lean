import LeanLongfellow.Circuit.SHA256Round
import Mathlib.Tactic.FinCases

open Finset

/-! # SHA-256 Compression Function

Message schedule, 64-round compression, final addition, and single-block
SHA-256 — all as constraint relations over a prime field.
-/

set_option autoImplicit false

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: SHA-256 Constants (typeclass)
-- ============================================================

/-- SHA-256 round constants (64 values) and initial hash values (8 values).
    Axiomatized — concrete values are specific 32-bit integers from the spec. -/
class SHA256Constants (F : Type*) [Field F] where
  /-- Round constants K_0 .. K_63. -/
  K : Fin 64 → (Fin 32 → F)
  /-- Initial hash values H_0 .. H_7. -/
  H_init : Fin 8 → (Fin 32 → F)
  /-- Each round constant is a valid 32-bit word. -/
  K_valid : ∀ i, isWord32 (K i)
  /-- Each initial hash value is a valid 32-bit word. -/
  H_init_valid : ∀ i, isWord32 (H_init i)

-- ============================================================
-- Section 2: Message Schedule
-- ============================================================

/-- Message schedule: 64 words derived from 16 input words.
    W_i for i < 16 are the input message block.
    W_i for i ≥ 16: W_i = σ1(W_{i-2}) + W_{i-7} + σ0(W_{i-15}) + W_{i-16}
    (mod 2^32). -/
def messageScheduleConstraint (W : Fin 64 → (Fin 32 → F))
    (input : Fin 16 → (Fin 32 → F)) : Prop :=
  -- First 16 words are the input
  (∀ i : Fin 16, W ⟨i.val, by omega⟩ = input i) ∧
  -- All words are valid
  (∀ i : Fin 64, isWord32 (W i)) ∧
  -- Expansion for i ≥ 16
  (∀ i : Fin 64, 16 ≤ i.val →
    ∃ carry : F,
      word32Val (sha256SmallSigma1 (W ⟨i.val - 2, by omega⟩)) +
      word32Val (W ⟨i.val - 7, by omega⟩) +
      word32Val (sha256SmallSigma0 (W ⟨i.val - 15, by omega⟩)) +
      word32Val (W ⟨i.val - 16, by omega⟩) =
      word32Val (W i) + carry * (2 : F) ^ 32)

/-- All message-schedule words are valid 32-bit words. -/
theorem messageSchedule_valid (W : Fin 64 → (Fin 32 → F))
    (input : Fin 16 → (Fin 32 → F))
    (h : messageScheduleConstraint W input) :
    ∀ i, isWord32 (W i) := h.2.1

-- ============================================================
-- Section 3: SHA-256 Compression (64 rounds)
-- ============================================================

/-- Carry witnesses for a single round: (carry_t2, carry_a, carry_e). -/
abbrev RoundCarries (F : Type*) := F × F × F

/-- SHA-256 compression: 64 rounds applied to initial state.
    states(0) = initial state from SHA256Constants.H_init,
    states(i+1) = round(states(i), K_i, W_i). -/
def sha256Compression [SHA256Constants F]
    (W : Fin 64 → (Fin 32 → F))
    (states : Fin 65 → SHA256State F)
    (t1s t2s : Fin 64 → (Fin 32 → F))
    (carries : Fin 64 → RoundCarries F) : Prop :=
  -- Initial state from constants
  states ⟨0, by omega⟩ = {
    a := SHA256Constants.H_init 0, b := SHA256Constants.H_init 1,
    c := SHA256Constants.H_init 2, d := SHA256Constants.H_init 3,
    e := SHA256Constants.H_init 4, f := SHA256Constants.H_init 5,
    g := SHA256Constants.H_init 6, h := SHA256Constants.H_init 7
  } ∧
  -- Each round step is valid
  ∀ i : Fin 64,
    sha256RoundConstraint (states i.castSucc) (states i.succ)
      (SHA256Constants.K i) (W i) (t1s i) (t2s i)
      (carries i).1 (carries i).2.1 (carries i).2.2

-- ============================================================
-- Section 4: Final Addition
-- ============================================================

/-- SHA-256 final addition: output = H_init + final_state (mod 2^32)
    for each of the 8 state words. -/
def sha256FinalAdd [SHA256Constants F]
    (finalState : SHA256State F) (output : Fin 8 → (Fin 32 → F))
    (carries : Fin 8 → F) : Prop :=
  word32Add (SHA256Constants.H_init 0) finalState.a (output 0) (carries 0) ∧
  word32Add (SHA256Constants.H_init 1) finalState.b (output 1) (carries 1) ∧
  word32Add (SHA256Constants.H_init 2) finalState.c (output 2) (carries 2) ∧
  word32Add (SHA256Constants.H_init 3) finalState.d (output 3) (carries 3) ∧
  word32Add (SHA256Constants.H_init 4) finalState.e (output 4) (carries 4) ∧
  word32Add (SHA256Constants.H_init 5) finalState.f (output 5) (carries 5) ∧
  word32Add (SHA256Constants.H_init 6) finalState.g (output 6) (carries 6) ∧
  word32Add (SHA256Constants.H_init 7) finalState.h (output 7) (carries 7)

/-- Each output word from the final addition is a valid 32-bit word. -/
theorem sha256FinalAdd_valid [SHA256Constants F]
    (finalState : SHA256State F) (output : Fin 8 → (Fin 32 → F))
    (carries : Fin 8 → F)
    (h : sha256FinalAdd finalState output carries) :
    ∀ i : Fin 8, isWord32 (output i) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro i; fin_cases i
  · exact h0.1
  · exact h1.1
  · exact h2.1
  · exact h3.1
  · exact h4.1
  · exact h5.1
  · exact h6.1
  · exact h7.1

-- ============================================================
-- Section 5: Full SHA-256 (single block)
-- ============================================================

/-- SHA-256 hash of a single 512-bit block (16 × 32-bit words).
    Constrains: input → message schedule → 64 rounds → final addition → output. -/
def sha256SingleBlock [SHA256Constants F]
    (input : Fin 16 → (Fin 32 → F))
    (output : Fin 8 → (Fin 32 → F)) : Prop :=
  ∃ (W : Fin 64 → (Fin 32 → F))
    (states : Fin 65 → SHA256State F)
    (t1s t2s : Fin 64 → (Fin 32 → F))
    (roundCarries : Fin 64 → RoundCarries F)
    (finalCarries : Fin 8 → F),
  messageScheduleConstraint W input ∧
  sha256Compression W states t1s t2s roundCarries ∧
  sha256FinalAdd (states ⟨64, by omega⟩) output finalCarries

-- ============================================================
-- Section 6: Validity Theorem
-- ============================================================

/-- If SHA-256 constraints are satisfied with valid input, the output is valid. -/
theorem sha256SingleBlock_valid [SHA256Constants F]
    (input : Fin 16 → (Fin 32 → F)) (output : Fin 8 → (Fin 32 → F))
    (_hinput : ∀ i, isWord32 (input i))
    (h : sha256SingleBlock input output) :
    ∀ i, isWord32 (output i) := by
  obtain ⟨_W, _states, _t1s, _t2s, _rc, finalCarries, _, _, hfinal⟩ := h
  exact sha256FinalAdd_valid _ _ finalCarries hfinal
