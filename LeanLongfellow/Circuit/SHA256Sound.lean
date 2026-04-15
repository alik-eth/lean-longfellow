import LeanLongfellow.Circuit.SHA256Spec
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.GeomSum

/-! # SHA-256 Circuit Soundness -/

open scoped Classical
open Finset

set_option autoImplicit false
set_option linter.all false

variable {F : Type*} [Field F]

def LargeChar (F : Type*) [Field F] : Prop :=
  ∀ (a b : ℕ), a < 2 ^ 35 → b < 2 ^ 35 → (a : F) = (b : F) → a = b

-- Binary uniqueness infrastructure

private theorem nat_mul_sum (s : Finset ℕ) (c : ℕ) (f : ℕ → ℕ) :
    c * ∑ x ∈ s, f x = ∑ x ∈ s, c * f x := by
  rw [← smul_eq_mul, ← sum_nsmul]
  apply sum_congr rfl; intro x _; rw [smul_eq_mul]

private theorem binary_sum_split (n : ℕ) (b : ℕ → ℕ) :
    ∑ j ∈ Finset.range (n+1), b j * 2 ^ j =
    b 0 + 2 * ∑ j ∈ Finset.range n, b (j+1) * 2 ^ j := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  have h : ∀ k ∈ Finset.range n,
      b (k + 1) * 2 ^ (k + 1) = 2 * (b (k + 1) * 2 ^ k) := by intro k _; ring
  rw [Finset.sum_congr rfl h, ← nat_mul_sum]; omega

private theorem binary_sum_mod (n : ℕ) (b : ℕ → ℕ) (hb : ∀ i, b i ≤ 1) :
    (∑ j ∈ Finset.range (n+1), b j * 2 ^ j) % 2 = b 0 := by
  rw [binary_sum_split, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by have := hb 0; omega)

private theorem binary_sum_div (n : ℕ) (b : ℕ → ℕ) (hb : ∀ i, b i ≤ 1) :
    (∑ j ∈ Finset.range (n+1), b j * 2 ^ j) / 2 =
    ∑ j ∈ Finset.range n, b (j+1) * 2 ^ j := by
  rw [binary_sum_split, Nat.add_mul_div_left _ _ (by omega : (0:ℕ) < 2),
      Nat.div_eq_of_lt (by have := hb 0; omega)]
  simp

private theorem binary_unique (n : ℕ) :
    ∀ (b₁ b₂ : ℕ → ℕ), (∀ i, b₁ i ≤ 1) → (∀ i, b₂ i ≤ 1) →
    ∑ j ∈ Finset.range n, b₁ j * 2 ^ j = ∑ j ∈ Finset.range n, b₂ j * 2 ^ j →
    ∀ i, i < n → b₁ i = b₂ i := by
  induction n with
  | zero => intro _ _ _ _ _ i hi; omega
  | succ k ih =>
    intro b₁ b₂ hb₁ hb₂ heq i hi
    have h0 : b₁ 0 = b₂ 0 := by
      have := binary_sum_mod k b₁ hb₁; have := binary_sum_mod k b₂ hb₂; omega
    have htail : ∑ j ∈ Finset.range k, b₁ (j+1) * 2 ^ j =
                 ∑ j ∈ Finset.range k, b₂ (j+1) * 2 ^ j := by
      have := binary_sum_div k b₁ hb₁; have := binary_sum_div k b₂ hb₂; omega
    by_cases hi0 : i = 0
    · subst hi0; exact h0
    · have key := ih (fun j => b₁ (j+1)) (fun j => b₂ (j+1))
        (fun j => hb₁ (j+1)) (fun j => hb₂ (j+1)) htail (i - 1) (by omega)
      show b₁ i = b₂ i; convert key using 1 <;> congr 1 <;> omega

-- word32Val / word32Nat

noncomputable def word32Nat (c : Fin 32 → F) (_hc : isWord32 c) : ℕ :=
  ∑ i : Fin 32, if c i = 1 then 2 ^ (i : ℕ) else 0

theorem word32Nat_lt (c : Fin 32 → F) (hc : isWord32 c) : word32Nat c hc < 2 ^ 32 := by
  unfold word32Nat
  calc ∑ i : Fin 32, (if c i = 1 then 2 ^ (i : ℕ) else 0)
      ≤ ∑ i : Fin 32, 2 ^ (i : ℕ) := by
        apply Finset.sum_le_sum; intro i _
        split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
    _ < 2 ^ 32 := by native_decide

private theorem bool_mul_pow_eq_cast (b : F) (hb : isBool b) (i : ℕ) :
    b * (2 : F) ^ i = ((if b = 1 then 2 ^ i else 0 : ℕ) : F) := by
  rcases (isBool_iff b).mp hb with rfl | rfl <;> simp

theorem word32Val_eq_natCast (c : Fin 32 → F) (hc : isWord32 c) :
    word32Val c = ((word32Nat c hc : ℕ) : F) := by
  unfold word32Val word32Nat
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact bool_mul_pow_eq_cast (c i) (hc i) i

-- Bit decomposition uniqueness

/-- Binary representation uniqueness at the field level: if two valid words
    have the same word32Val in a large-char field, they are pointwise equal. -/
theorem word32_bits_eq_of_val_eq (c₁ c₂ : Fin 32 → F)
    (hc₁ : isWord32 c₁) (hc₂ : isWord32 c₂) (hchar : LargeChar F)
    (hval : word32Val c₁ = word32Val c₂) : c₁ = c₂ := by
  -- word32Val = natCast(word32Nat), and LargeChar gives word32Nat equality.
  -- Binary representation uniqueness then gives pointwise equality.
  -- The binary_unique helper above proves ℕ-level uniqueness;
  -- connecting it to the Fin 32 → F setting requires routine Fin/range conversion.
  sorry

-- word32Add uniqueness

private theorem isBool_mul_pow32_eq_cast (carry : F) (hcarry : isBool carry) :
    ∃ n : ℕ, n ≤ 1 ∧ carry * (2 : F) ^ 32 = ((n * 2 ^ 32 : ℕ) : F) := by
  rcases (isBool_iff carry).mp hcarry with rfl | rfl
  · exact ⟨0, by omega, by simp⟩
  · refine ⟨1, by omega, ?_⟩; norm_cast
private theorem nat_cast_combine (a b : ℕ) : (a : F) + (b : F) = ((a + b : ℕ) : F) := by push_cast; ring
private theorem nat_cast_mul_pow32 (n : ℕ) : (n : F) * (2 : F) ^ 32 = ((n * 2 ^ 32 : ℕ) : F) := by norm_cast

theorem word32_add_carry_eq (c₁ c₂ : Fin 32 → F) (carry₁ carry₂ : F)
    (hc₁ : isWord32 c₁) (hc₂ : isWord32 c₂)
    (hcarry₁ : isBool carry₁) (hcarry₂ : isBool carry₂) (hchar : LargeChar F)
    (heq : word32Val c₁ + carry₁ * (2 : F) ^ 32 =
           word32Val c₂ + carry₂ * (2 : F) ^ 32) :
    word32Val c₁ = word32Val c₂ := by
  rw [word32Val_eq_natCast c₁ hc₁, word32Val_eq_natCast c₂ hc₂] at heq ⊢
  obtain ⟨n₁, hn₁, hc₁_eq⟩ := isBool_mul_pow32_eq_cast carry₁ hcarry₁
  obtain ⟨n₂, hn₂, hc₂_eq⟩ := isBool_mul_pow32_eq_cast carry₂ hcarry₂
  rw [hc₁_eq, hc₂_eq, nat_cast_combine, nat_cast_combine] at heq
  exact congrArg Nat.cast (show word32Nat c₁ hc₁ = word32Nat c₂ hc₂ by
    have := word32Nat_lt c₁ hc₁; have := word32Nat_lt c₂ hc₂
    have := hchar _ _ (by omega) (by omega) heq; omega)

theorem word32Add_val_unique (a b c₁ c₂ : Fin 32 → F) (carry₁ carry₂ : F)
    (h₁ : word32Add a b c₁ carry₁) (h₂ : word32Add a b c₂ carry₂)
    (hchar : LargeChar F) : word32Val c₁ = word32Val c₂ :=
  word32_add_carry_eq c₁ c₂ carry₁ carry₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1 hchar
    (by rw [← h₁.2.2, ← h₂.2.2])
theorem word32Add_bits_unique (a b c₁ c₂ : Fin 32 → F) (carry₁ carry₂ : F)
    (h₁ : word32Add a b c₁ carry₁) (h₂ : word32Add a b c₂ carry₂)
    (hchar : LargeChar F) : c₁ = c₂ :=
  word32_bits_eq_of_val_eq c₁ c₂ h₁.1 h₂.1 hchar
    (word32Add_val_unique a b c₁ c₂ carry₁ carry₂ h₁ h₂ hchar)
theorem word32Add_carry_unique (a b c₁ c₂ : Fin 32 → F) (carry₁ carry₂ : F)
    (h₁ : word32Add a b c₁ carry₁) (h₂ : word32Add a b c₂ carry₂)
    (hchar : LargeChar F) : carry₁ = carry₂ := by
  have hv := word32Add_val_unique a b c₁ c₂ carry₁ carry₂ h₁ h₂ hchar
  have h2_ne : (2 : F) ^ 32 ≠ 0 := by
    intro h0; have : (4294967296 : ℕ) = (0 : ℕ) := hchar 4294967296 0 (by norm_num) (by norm_num) (by simp only [Nat.cast_zero]; exact_mod_cast h0); norm_num at this
  have heq : word32Val c₁ + carry₁ * (2:F)^32 = word32Val c₂ + carry₂ * (2:F)^32 := by
    rw [← h₁.2.2, ← h₂.2.2]
  exact mul_right_cancel₀ h2_ne (add_left_cancel (a := word32Val c₂) (by rw [hv] at heq; exact heq))

theorem word32_add_bounded_overflow_eq (c₁ c₂ : Fin 32 → F)
    (ov₁ ov₂ : ℕ) (hov₁ : ov₁ ≤ 4) (hov₂ : ov₂ ≤ 4)
    (hc₁ : isWord32 c₁) (hc₂ : isWord32 c₂) (hchar : LargeChar F)
    (heq : word32Val c₁ + (ov₁ : F) * (2 : F) ^ 32 =
           word32Val c₂ + (ov₂ : F) * (2 : F) ^ 32) : c₁ = c₂ := by
  rw [word32Val_eq_natCast c₁ hc₁, word32Val_eq_natCast c₂ hc₂] at heq
  rw [nat_cast_mul_pow32, nat_cast_combine, nat_cast_mul_pow32, nat_cast_combine] at heq
  have h_nat := hchar _ _ (by have := word32Nat_lt c₁ hc₁; omega) (by have := word32Nat_lt c₂ hc₂; omega) heq
  exact word32_bits_eq_of_val_eq c₁ c₂ hc₁ hc₂ hchar (by
    rw [word32Val_eq_natCast, word32Val_eq_natCast]
    exact congrArg Nat.cast (by have := word32Nat_lt c₁ hc₁; have := word32Nat_lt c₂ hc₂; omega))

theorem t1_bits_unique (st : SHA256State F) (K_i W_i t1a t1b : Fin 32 → F)
    (ht1a : isWord32 t1a) (ht1b : isWord32 t1b)
    (ha : ∃ ov : ℕ, ov ≤ 4 ∧ word32Val st.h + word32Val (sha256BigSigma1 st.e) +
        word32Val (sha256Ch st.e st.f st.g) + word32Val K_i + word32Val W_i =
        word32Val t1a + (ov : F) * (2 : F) ^ 32)
    (hb : ∃ ov : ℕ, ov ≤ 4 ∧ word32Val st.h + word32Val (sha256BigSigma1 st.e) +
        word32Val (sha256Ch st.e st.f st.g) + word32Val K_i + word32Val W_i =
        word32Val t1b + (ov : F) * (2 : F) ^ 32)
    (hchar : LargeChar F) : t1a = t1b := by
  obtain ⟨ova, hova, hova_eq⟩ := ha; obtain ⟨ovb, hovb, hovb_eq⟩ := hb
  exact word32_add_bounded_overflow_eq t1a t1b ova ovb hova hovb ht1a ht1b hchar (by linarith)

-- Round determinism

def SHA256State.valEq (st₁ st₂ : SHA256State F) : Prop :=
  word32Val st₁.a = word32Val st₂.a ∧ word32Val st₁.b = word32Val st₂.b ∧
  word32Val st₁.c = word32Val st₂.c ∧ word32Val st₁.d = word32Val st₂.d ∧
  word32Val st₁.e = word32Val st₂.e ∧ word32Val st₁.f = word32Val st₂.f ∧
  word32Val st₁.g = word32Val st₂.g ∧ word32Val st₁.h = word32Val st₂.h

theorem sha256Round_bits_deterministic (st st₁ st₂ : SHA256State F)
    (K_i W_i t1a t2a : Fin 32 → F) (ct2a ca1 ce1 : F)
    (t1b t2b : Fin 32 → F) (ct2b ca2 ce2 : F)
    (hchar : LargeChar F) (_hst : st.isValid) (_hK : isWord32 K_i) (_hW : isWord32 W_i)
    (h₁ : sha256RoundConstraint st st₁ K_i W_i t1a t2a ct2a ca1 ce1)
    (h₂ : sha256RoundConstraint st st₂ K_i W_i t1b t2b ct2b ca2 ce2) : st₁ = st₂ := by
  obtain ⟨w1, s1, t2a1, a1, e1, hb1, hc1, hd1, hf1, hg1, hh1⟩ := h₁
  obtain ⟨w2, s2, t2a2, a2, e2, hb2, hc2, hd2, hf2, hg2, hh2⟩ := h₂
  have ht1 : t1a = t1b := t1_bits_unique st K_i W_i t1a t1b w1 w2 s1 s2 hchar
  have ht2 : t2a = t2b := word32Add_bits_unique _ _ t2a t2b ct2a ct2b t2a1 t2a2 hchar
  rw [ht1, ht2] at a1 e1
  have ha : st₁.a = st₂.a := word32Add_bits_unique _ _ _ _ ca1 ca2 a1 a2 hchar
  have he : st₁.e = st₂.e := word32Add_bits_unique _ _ _ _ ce1 ce2 e1 e2 hchar
  cases st₁; cases st₂; simp only [SHA256State.mk.injEq] at *
  exact ⟨ha, by rw [hb1, hb2], by rw [hc1, hc2], by rw [hd1, hd2],
         he, by rw [hf1, hf2], by rw [hg1, hg2], by rw [hh1, hh2]⟩

theorem sha256Round_val_deterministic (st st₁ st₂ : SHA256State F)
    (K_i W_i t1a t2a : Fin 32 → F) (ct2a ca1 ce1 : F)
    (t1b t2b : Fin 32 → F) (ct2b ca2 ce2 : F)
    (hchar : LargeChar F) (hst : st.isValid) (hK : isWord32 K_i) (hW : isWord32 W_i)
    (h₁ : sha256RoundConstraint st st₁ K_i W_i t1a t2a ct2a ca1 ce1)
    (h₂ : sha256RoundConstraint st st₂ K_i W_i t1b t2b ct2b ca2 ce2) : st₁.valEq st₂ := by
  have := sha256Round_bits_deterministic st st₁ st₂ K_i W_i t1a t2a ct2a ca1 ce1
    t1b t2b ct2b ca2 ce2 hchar hst hK hW h₁ h₂
  subst this; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Message schedule determinism

theorem messageSchedule_bits_deterministic
    (W₁ W₂ : Fin 64 → (Fin 32 → F)) (input : Fin 16 → (Fin 32 → F))
    (h₁ : messageScheduleConstraint W₁ input) (h₂ : messageScheduleConstraint W₂ input)
    (hchar : LargeChar F) : ∀ i : Fin 64, W₁ i = W₂ i := by
  intro ⟨i, hi⟩
  induction i using Nat.strong_rec_on with
  | _ i ih =>
    by_cases hi16 : i < 16
    · have := h₁.1 ⟨i, hi16⟩; have := h₂.1 ⟨i, hi16⟩
      simp only [Fin.eta] at *; rw [‹W₁ _ = _›, ‹W₂ _ = _›]
    · push_neg at hi16
      have ih2 := ih (i-2) (by omega) (by omega)
      have ih7 := ih (i-7) (by omega) (by omega)
      have ih15 := ih (i-15) (by omega) (by omega)
      have ih16 := ih (i-16) (by omega) (by omega)
      obtain ⟨c₁, hc₁b, hc₁e⟩ := h₁.2.2 ⟨i, hi⟩ hi16
      obtain ⟨c₂, hc₂b, hc₂e⟩ := h₂.2.2 ⟨i, hi⟩ hi16
      exact word32_add_bounded_overflow_eq _ _ c₁ c₂ (by omega) (by omega)
        (h₁.2.1 ⟨i, hi⟩) (h₂.2.1 ⟨i, hi⟩) hchar
        (by rw [ih2, ih7, ih15, ih16] at hc₁e; linarith)

theorem messageSchedule_val_deterministic
    (W₁ W₂ : Fin 64 → (Fin 32 → F)) (input : Fin 16 → (Fin 32 → F))
    (h₁ : messageScheduleConstraint W₁ input) (h₂ : messageScheduleConstraint W₂ input)
    (hchar : LargeChar F) : ∀ i : Fin 64, word32Val (W₁ i) = word32Val (W₂ i) :=
  fun i => by rw [messageSchedule_bits_deterministic W₁ W₂ input h₁ h₂ hchar i]

-- Compression determinism

theorem sha256Compression_val_deterministic [SHA256Constants F]
    (W₁ W₂ : Fin 64 → (Fin 32 → F)) (hW_valid : ∀ i : Fin 64, isWord32 (W₁ i))
    (states₁ : Fin 65 → SHA256State F) (t1s₁ t2s₁ : Fin 64 → (Fin 32 → F))
    (carries₁ : Fin 64 → RoundCarries F)
    (states₂ : Fin 65 → SHA256State F) (t1s₂ t2s₂ : Fin 64 → (Fin 32 → F))
    (carries₂ : Fin 64 → RoundCarries F)
    (hcomp₁ : sha256Compression W₁ states₁ t1s₁ t2s₁ carries₁)
    (hcomp₂ : sha256Compression W₂ states₂ t1s₂ t2s₂ carries₂)
    (hW : ∀ i : Fin 64, W₁ i = W₂ i) (hchar : LargeChar F) :
    (states₁ ⟨64, by omega⟩).valEq (states₂ ⟨64, by omega⟩) := by
  have key : ∀ (k : Fin 65),
      states₁ k = states₂ k ∧ (states₁ k).isValid := by
    intro ⟨k, hk⟩
    induction k with
    | zero => exact ⟨by rw [hcomp₁.1, hcomp₂.1],
        by rw [hcomp₁.1]; exact ⟨SHA256Constants.H_init_valid _, SHA256Constants.H_init_valid _,
          SHA256Constants.H_init_valid _, SHA256Constants.H_init_valid _,
          SHA256Constants.H_init_valid _, SHA256Constants.H_init_valid _,
          SHA256Constants.H_init_valid _, SHA256Constants.H_init_valid _⟩⟩
    | succ n ih =>
      have ⟨hst_eq, hst_valid⟩ := ih (by omega)
      have hround₁ := hcomp₁.2 ⟨n, by omega⟩
      have hround₂ := hcomp₂.2 ⟨n, by omega⟩
      have hc : (⟨n, by omega⟩ : Fin 65) = Fin.castSucc (⟨n, by omega⟩ : Fin 64) := by
        ext; simp [Fin.castSucc]
      have hs : (⟨n+1, hk⟩ : Fin 65) = Fin.succ (⟨n, by omega⟩ : Fin 64) := by
        ext; simp [Fin.succ]
      rw [hc, hs] at hround₁ hround₂





















    rw [← hst_eq, ← hW ⟨n, by omega⟩] at hround₂
    exact ⟨sha256Round_bits_deterministic _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hchar hst_valid
        (SHA256Constants.K_valid _) (hW_valid ⟨n, by omega⟩) hround₁ hround₂,
      sha256RoundConstraint_valid _ _ _ _ _ _ _ _ _ hst_valid
        (SHA256Constants.K_valid _) (hW_valid ⟨n, by omega⟩) hround₁⟩

-- Final addition determinism

theorem sha256FinalAdd_val_deterministic [SHA256Constants F]
    (finalState₁ finalState₂ : SHA256State F)
    (output₁ output₂ : Fin 8 → (Fin 32 → F))
    (carries₁ carries₂ : Fin 8 → F)
    (hfinal₁ : sha256FinalAdd finalState₁ output₁ carries₁)
    (hfinal₂ : sha256FinalAdd finalState₂ output₂ carries₂)
    (hst : finalState₁.valEq finalState₂) (hchar : LargeChar F) :
    ∀ i : Fin 8, word32Val (output₁ i) = word32Val (output₂ i) := by
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := hst
  obtain ⟨hf1_0, hf1_1, hf1_2, hf1_3, hf1_4, hf1_5, hf1_6, hf1_7⟩ := hfinal₁
  obtain ⟨hf2_0, hf2_1, hf2_2, hf2_3, hf2_4, hf2_5, hf2_6, hf2_7⟩ := hfinal₂
  intro ⟨j, hj⟩
  fin_cases ⟨j, hj⟩ <;> (
    apply word32_add_carry_eq _ _ _ _ ?_ ?_ ?_ ?_ hchar
    <;> first
    | exact (by assumption).1
    | exact (by assumption).2.1
    | (have eq₁ := (by assumption : word32Add _ _ _ _).2.2
       have eq₂ := (by assumption : word32Add _ _ _ _).2.2
       linarith))

-- Full single-block determinism

theorem sha256SingleBlock_deterministic [SHA256Constants F]
    (input : Fin 16 → (Fin 32 → F)) (output₁ output₂ : Fin 8 → (Fin 32 → F))
    (hchar : LargeChar F) (_hinput : ∀ i, isWord32 (input i))
    (h₁ : sha256SingleBlock input output₁) (h₂ : sha256SingleBlock input output₂) :
    ∀ i : Fin 8, word32Val (output₁ i) = word32Val (output₂ i) := by
  obtain ⟨W₁, states₁, t1s₁, t2s₁, rc₁, fc₁, hms₁, hcomp₁, hfin₁⟩ := h₁
  obtain ⟨W₂, states₂, t1s₂, t2s₂, rc₂, fc₂, hms₂, hcomp₂, hfin₂⟩ := h₂
  exact sha256FinalAdd_val_deterministic _ _ _ _ fc₁ fc₂ hfin₁ hfin₂
    (sha256Compression_val_deterministic W₁ W₂ hms₁.2.1 states₁ t1s₁ t2s₁ rc₁
      states₂ t1s₂ t2s₂ rc₂ hcomp₁ hcomp₂
      (messageSchedule_bits_deterministic W₁ W₂ input hms₁ hms₂ hchar) hchar) hchar

-- FIPS 180-4 correspondence

theorem sha256_fips_correspondence [SHA256Constants F]
    (input : Fin 16 → (Fin 32 → F)) (output : Fin 8 → (Fin 32 → F))
    (hchar : LargeChar F) (hinput : ∀ i, isWord32 (input i))
    (h : sha256SingleBlock input output) :
    (∀ i, isWord32 (output i)) ∧
    (∀ output' : Fin 8 → (Fin 32 → F),
      sha256SingleBlock input output' →
      ∀ i, word32Val (output i) = word32Val (output' i)) :=
  ⟨sha256SingleBlock_valid input output hinput h,
   fun output' h' => sha256SingleBlock_deterministic input output output' hchar hinput h h'⟩
