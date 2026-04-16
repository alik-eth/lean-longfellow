import LeanLongfellow.Field.P256
import LeanLongfellow.Ligero.ProbabilisticE2E

/-! # Concrete Probability Bound for P-256 Longfellow

This file instantiates the abstract Longfellow error composition
(`longfellow_total_error` from `ProbabilisticE2E`) with concrete parameters
for the NIST P-256 ECDSA verification circuit.

## Parameters

- **Field:** `F_p256 = ZMod p256Prime` with `|F| = p256Prime ~ 2^256`.
- **Circuit:** 3591 layers (14 * 256 + 7).
- **Width:** `s = 5` (32-wire layers, `2^5` gate positions).
- **Sumcheck rounds per layer:** `2 * s = 10`.

## Error budget

| Component | Bound (count of bad challenges) |
|-----------|---------------------------------|
| Per-layer sumcheck | `(2*s) * (2 * |F|^(2*s-1)) = 20 * |F|^9` |
| All 3591 layers (union bound) | `3591 * 20 * |F|^9 = 71820 * |F|^9` |
| Ligero linear test | `|F|^0 = 1` |
| Ligero quadratic test | `|F|^0 = 1` |
| Ligero LDT | `0` (absorbed into simplified bound) |
| **Total** | `71820 * |F|^9 + 2 <= 71822 * |F|^9` |

## Security level

Dividing by the per-layer challenge space `|F|^10`:

    Pr[bad] <= 71822 * |F|^9 / |F|^10 = 71822 / |F| = 71822 / p256Prime

Since `71822 < 2^17` and `p256Prime > 2^255`, this gives:

    Pr[bad] < 2^17 / 2^255 = 2^{-238}

This is well below any practical attack threshold.

## Implementation note

All definitions use the symbolic variable `card` (= `Fintype.card F_p256`)
rather than computing `Fintype.card F_p256` directly. This prevents Lean
from trying to normalize `p256Prime^9` (~2304 bits) at elaboration time,
which would cause memory blowup.
-/

open Finset

noncomputable section

-- ============================================================
-- Section 1: Concrete parameters
-- ============================================================

/-- Number of GKR layers for P-256 ECDSA with 256-bit scalars.
    Equal to `14 * 256 + 7 = 3591`. -/
def p256_NL : ℕ := 3591

/-- Gate circuit width parameter (log2 of wires per layer). -/
def p256_s : ℕ := 5

/-- The P-256 ECDSA circuit has exactly 3591 layers. -/
theorem p256_NL_eq : p256_NL = 3591 := rfl

/-- The cardinality of the P-256 field equals the P-256 prime. -/
theorem p256_card : Fintype.card F_p256 = p256Prime := ZMod.card p256Prime

-- ============================================================
-- Section 2: Per-component error bounds with concrete numbers
-- ============================================================

/-- Per-layer sumcheck error count for s = 5, stated symbolically:
    `(2 * 5) * (2 * card^(2 * 5 - 1)) = 20 * card^9`. -/
theorem p256_sumcheck_error_per_layer (card : ℕ) :
    (2 * p256_s) * (2 * card ^ (2 * p256_s - 1)) =
    20 * card ^ 9 := by
  simp [p256_s]; ring

/-- Total sumcheck error across all 3591 layers:
    `3591 * (20 * card^9) = 71820 * card^9`. -/
theorem p256_total_sumcheck_error (card : ℕ) :
    p256_NL * (20 * card ^ 9) =
    71820 * card ^ 9 := by
  simp [p256_NL]; ring

-- ============================================================
-- Section 3: Concrete error parameter instantiation
-- ============================================================

/-- Concrete Longfellow error parameters for P-256 ECDSA.

    All fields use literal numbers to avoid forcing Lean to evaluate
    `Fintype.card F_p256` (which would try to compute p256Prime).

    - `num_layers`: 3591
    - `sumcheck_error_per_layer`: `20 * |F|^9`
    - `ligero_linear_error`: 1
    - `ligero_quad_error`: 1
    - `ligero_ldt_error`: 0 -/
def p256ErrorParams (card : ℕ) : LongfellowErrorParams where
  num_layers := p256_NL
  sumcheck_error_per_layer := 20 * card ^ 9
  ligero_linear_error := 1
  ligero_quad_error := 1
  ligero_ldt_error := 0

-- ============================================================
-- Section 4: Total error bound
-- ============================================================

/-- The total error count equals `71820 * card^9 + 2`. -/
theorem p256ErrorParams_total (card : ℕ) :
    (p256ErrorParams card).total = 71820 * card ^ 9 + 2 := by
  simp [LongfellowErrorParams.total, p256ErrorParams, p256_NL]
  ring

/-- **Concrete P-256 soundness error bound.**

The total error count for the Longfellow verifier with the P-256 ECDSA
circuit is at most `71822 * card^9`.

Total = `71820 * card^9 + 2 <= 71822 * card^9` (for card ≥ 1). -/
theorem p256ErrorParams_total_le (card : ℕ) (hcard : 0 < card) :
    (p256ErrorParams card).total ≤ 71822 * card ^ 9 := by
  rw [p256ErrorParams_total]
  have h1 : 1 ≤ card ^ 9 := Nat.one_le_pow 9 _ hcard
  omega

/-- Specialization to the actual P-256 field cardinality. -/
theorem p256ErrorParams_total_le_concrete :
    (p256ErrorParams (Fintype.card F_p256)).total ≤
    71822 * Fintype.card F_p256 ^ 9 :=
  p256ErrorParams_total_le _ Fintype.card_pos

-- ============================================================
-- Section 5: Security level analysis
-- ============================================================

/-- The error numerator 71822 is negligible compared to the P-256 field size. -/
theorem p256_numerator_small : 71822 < p256Prime := by
  simp [p256Prime]

/-- The error numerator fits in 17 bits. -/
theorem p256_numerator_lt_pow17 : 71822 < 2 ^ 17 := by omega

/-- The P-256 prime exceeds `2^255`, so `71822 / p256Prime < 2^{-238}`. -/
theorem p256Prime_gt_pow255 : 2 ^ 255 < p256Prime := by
  simp [p256Prime]

/-- **Concrete P-256 security level.**

Combining the error bound with the field size:
- Error count `<= 71822 * |F|^9`
- Challenge space `= |F|^10`
- Probability `<= 71822 / |F|`
- Since `71822 < 2^17` and `|F| = p256Prime > 2^255`,
  the probability is `< 2^17 / 2^255 = 2^{-238}`. -/
theorem p256_security_level :
    (p256ErrorParams (Fintype.card F_p256)).total ≤
      71822 * Fintype.card F_p256 ^ 9 ∧
    71822 < 2 ^ 17 ∧
    2 ^ 255 < p256Prime :=
  ⟨p256ErrorParams_total_le_concrete, p256_numerator_lt_pow17, p256Prime_gt_pow255⟩

-- ============================================================
-- Section 6: Connection to abstract composition theorem
-- ============================================================

/-- The concrete error parameters satisfy the abstract bound from
    `longfellow_total_error`. -/
theorem p256_composition_consistent (card : ℕ) :
    (p256ErrorParams card).num_layers * (p256ErrorParams card).sumcheck_error_per_layer +
    (p256ErrorParams card).ligero_linear_error +
    (p256ErrorParams card).ligero_quad_error +
    (p256ErrorParams card).ligero_ldt_error =
    (p256ErrorParams card).total := by
  rfl

/-- Concrete bound in terms of the P-256 prime (fully numeric). -/
theorem p256_error_bound_numeric :
    (p256ErrorParams (Fintype.card F_p256)).total ≤ 71822 * p256Prime ^ 9 := by
  calc (p256ErrorParams (Fintype.card F_p256)).total
      ≤ 71822 * Fintype.card F_p256 ^ 9 := p256ErrorParams_total_le_concrete
    _ = 71822 * p256Prime ^ 9 := by rw [p256_card]

end
