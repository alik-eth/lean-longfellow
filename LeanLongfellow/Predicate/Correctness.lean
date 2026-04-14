import LeanLongfellow.Predicate.Defs

/-! # zk-eIDAS Predicate Correctness

Basic properties of the six zk-eIDAS predicates and the equivalence between
the algebraic (circuit) set-membership check and the semantic one. -/

open Finset

variable {F : Type*}

-- ============================================================
-- Section 1: Range ↔ GTE ∧ LTE
-- ============================================================

theorem range_iff_gte_and_lte [LinearOrder F] (low high claim : F) :
    predicateHolds (.range low high) claim ↔
    predicateHolds (.gte low) claim ∧ predicateHolds (.lte high) claim := by
  simp [predicateHolds]

-- ============================================================
-- Section 2: NEQ ↔ ¬ EQ
-- ============================================================

theorem neq_iff_not_eq [LinearOrder F] (expected claim : F) :
    predicateHolds (.neq expected) claim ↔
    ¬ predicateHolds (.eq expected) claim := by
  simp [predicateHolds]

-- ============================================================
-- Section 3: Singleton set membership ↔ EQ
-- ============================================================

theorem set_member_singleton_iff_eq [LinearOrder F] (v claim : F) :
    predicateHolds (.set_member [v]) claim ↔
    predicateHolds (.eq v) claim := by
  simp [predicateHolds]

-- ============================================================
-- Section 4: Empty set membership is always false
-- ============================================================

theorem set_member_empty_false [LinearOrder F] (claim : F) :
    ¬ predicateHolds (.set_member []) claim := by
  simp [predicateHolds]

-- ============================================================
-- Section 5: Range with low = high ↔ EQ
-- ============================================================

theorem range_point_iff_eq [LinearOrder F] (v claim : F) :
    predicateHolds (.range v v) claim ↔
    predicateHolds (.eq v) claim := by
  simp only [predicateHolds]
  constructor
  · exact fun ⟨h1, h2⟩ => le_antisymm h2 h1
  · exact fun h => ⟨le_of_eq h.symm, le_of_eq h⟩

-- ============================================================
-- Section 6: Circuit set membership ↔ semantic membership
-- ============================================================

/-- In a field (no zero divisors), a product of differences is zero iff some
    factor is zero, i.e. the claim equals some element in the set. -/
theorem circuitSetMember_iff_mem [Field F] {k : ℕ} (claim : F) (set : Fin k → F) :
    circuitSetMember claim set ↔ ∃ i : Fin k, claim = set i := by
  simp [circuitSetMember, Finset.prod_eq_zero_iff, sub_eq_zero]
