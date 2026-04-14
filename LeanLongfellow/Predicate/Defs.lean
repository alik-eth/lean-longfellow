import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Basic

/-! # zk-eIDAS Predicate Definitions

Formalizes the six predicate types used by zk-eIDAS for selective disclosure
of credential claims.  Values are modeled as field elements; ordered comparisons
require a `LinearOrderedField`. -/

open Finset

-- ============================================================
-- Section 1: Predicate operations
-- ============================================================

/-- Predicate operations supported by zk-eIDAS. -/
inductive PredicateOp where
  | gte | lte | eq | neq | range | set_member
  deriving DecidableEq

-- ============================================================
-- Section 2: Predicate specifications
-- ============================================================

/-- A predicate specification: the operation together with its public parameters.
    Parameterised by the field `F` of claim values. -/
inductive PredicateSpec (F : Type*) where
  | gte (threshold : F)
  | lte (threshold : F)
  | eq (expected : F)
  | neq (expected : F)
  | range (low high : F)
  | set_member (elems : List F)

-- ============================================================
-- Section 3: Semantic evaluation
-- ============================================================

/-- The semantic meaning of each predicate.
    Ordered predicates (gte, lte, range) require `LinearOrder F`. -/
def predicateHolds {F : Type*} [LinearOrder F] (spec : PredicateSpec F) (claim : F) : Prop :=
  match spec with
  | .gte threshold   => claim ≥ threshold
  | .lte threshold   => claim ≤ threshold
  | .eq expected     => claim = expected
  | .neq expected    => claim ≠ expected
  | .range low high  => low ≤ claim ∧ claim ≤ high
  | .set_member elems => claim ∈ elems

-- ============================================================
-- Section 4: Circuit-level set membership
-- ============================================================

/-- Circuit set membership: the product of (claim − set[i]) is zero iff the claim
    equals some set element.  This is the algebraic formulation used by circom. -/
def circuitSetMember {F : Type*} [Field F] {k : ℕ} (claim : F) (set : Fin k → F) : Prop :=
  ∏ i : Fin k, (claim - set i) = 0
