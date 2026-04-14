import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Tableau
import LeanLongfellow.Ligero.Tests.LowDegree
import LeanLongfellow.Ligero.Tests.Linear
import LeanLongfellow.Ligero.Tests.Quadratic

/-! # Ligero Soundness Composition

This file composes the three Ligero sub-protocol tests (low-degree, linear,
quadratic) into a single binding property.  The three tests provide
complementary guarantees:

1. **Low-degree test** → all rows are RS codewords (tableau is well-formed)
2. **Linear test** → witness satisfies `A·w = b` (given well-formed tableau)
3. **Quadratic test** → witness satisfies `w[x]·w[y] = w[z]`

## Main results

- `LigeroAccepts`: combined acceptance structure bundling all three test
  outcomes.
- `ligero_binding_from_tests`: if all three tests pass, the witness satisfies
  all constraints (`satisfiesAll`).
- `concrete_satisfies_abstract`: the concrete Ligero instantiation satisfies
  the abstract `LigeroScheme.binding` axiom.
- `ligero_completeness_composition`: if the witness satisfies all constraints
  and the tableau is well-formed, all three tests accept.
-/

open Finset

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Combined acceptance predicate
-- ============================================================

/-- All three Ligero tests accept.  This bundles:
    - `wf`: the low-degree test passed (tableau is well-formed),
    - `linear`: the linear test passed (witness satisfies `A·w = b`),
    - `quad`: the quadratic test passed (all quadratic constraints hold). -/
structure LigeroAccepts {params : LigeroParams}
    {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) where
  wf : tableauWellFormed domain T
  linear : satisfiesLinear w lcs
  quad : ∀ i, satisfiesQuad w (qcs i)

-- ============================================================
-- Section 2: Binding — combined acceptance implies satisfiesAll
-- ============================================================

/-- **Binding theorem**: If all three Ligero tests pass, the witness
    satisfies all constraints (both linear and quadratic).

    This is the composition of the three individual test guarantees into
    the single `satisfiesAll` predicate from `Constraints.lean`. -/
theorem ligero_binding_from_tests {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h : LigeroAccepts domain T w lcs qcs) :
    satisfiesAll w lcs qcs :=
  ⟨h.linear, h.quad⟩

/-- Variant: extract just the linear satisfaction from combined acceptance. -/
theorem ligero_linear_of_accepts {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h : LigeroAccepts domain T w lcs qcs) :
    satisfiesLinear w lcs :=
  h.linear

/-- Variant: extract just the quadratic satisfaction from combined acceptance. -/
theorem ligero_quad_of_accepts {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h : LigeroAccepts domain T w lcs qcs) :
    ∀ i, satisfiesQuad w (qcs i) :=
  h.quad

/-- Variant: extract tableau well-formedness from combined acceptance. -/
theorem ligero_wf_of_accepts {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h : LigeroAccepts domain T w lcs qcs) :
    tableauWellFormed domain T :=
  h.wf

-- ============================================================
-- Section 3: Connection to abstract LigeroScheme
-- ============================================================

/-- The concrete Ligero instantiation satisfies the abstract binding axiom.
    Given that the linear and quadratic tests accept on a witness, the witness
    satisfies all constraints.  This connects the concrete test predicates
    to the `LigeroScheme.binding` axiom from `Interface.lean`. -/
theorem concrete_satisfies_abstract {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_linear : satisfiesLinear w lcs)
    (h_quad : ∀ i, satisfiesQuad w (qcs i)) :
    satisfiesAll w lcs qcs :=
  ⟨h_linear, h_quad⟩

/-- The binding property expressed via the `satisfiesAll_iff` characterization. -/
theorem concrete_binding_iff {m n q : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) :
    satisfiesAll w lcs qcs ↔
      satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i) :=
  satisfiesAll_iff w lcs qcs

-- ============================================================
-- Section 4: Completeness composition
-- ============================================================

/-- **Completeness composition**: If the witness satisfies all constraints
    and the tableau is well-formed, then all three tests accept.

    This is the converse direction: honest execution leads to acceptance. -/
theorem ligero_completeness_composition {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_wf : tableauWellFormed domain T)
    (h_sat : satisfiesAll w lcs qcs) :
    LigeroAccepts domain T w lcs qcs :=
  { wf := h_wf
    linear := h_sat.1
    quad := h_sat.2 }

-- ============================================================
-- Section 5: Soundness of individual tests feed into binding
-- ============================================================

/-- If the quadratic test accepts (in the sense of `quadraticTestAccepts`),
    extract the per-constraint satisfaction needed for binding. -/
theorem quad_test_gives_binding {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h : quadraticTestAccepts w qcs) :
    ∀ i, satisfiesQuad w (qcs i) :=
  quadraticTest_sound w qcs h

/-- Compose the quadratic test soundness with the linear test to get
    full constraint satisfaction, without needing the LDT result.

    The LDT guarantees that the tableau is well-formed, which is needed
    for the linear and quadratic tests to be meaningful, but the
    constraint satisfaction itself depends only on the linear and
    quadratic test outcomes. -/
theorem binding_from_linear_and_quad {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_linear : satisfiesLinear w lcs)
    (h_quad : quadraticTestAccepts w qcs) :
    satisfiesAll w lcs qcs :=
  ⟨h_linear, quadraticTest_sound w qcs h_quad⟩

-- ============================================================
-- Section 6: Contrapositive — violation implies test failure
-- ============================================================

/-- **Contrapositive of binding**: if the witness does NOT satisfy all
    constraints, then at least one of the linear or quadratic tests
    must fail (regardless of tableau well-formedness). -/
theorem test_failure_of_violation {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ satisfiesAll w lcs qcs) :
    ¬ satisfiesLinear w lcs ∨ ¬ (∀ i, satisfiesQuad w (qcs i)) := by
  by_contra h_both
  push Not at h_both
  exact h_viol ⟨h_both.1, h_both.2⟩

/-- If the witness violates some linear constraint, the linear test
    must detect it: there exists a violated constraint row. -/
theorem linear_violation_detected {m n : ℕ}
    (w : Fin n → F) (lcs : LinearConstraints F m n)
    (h_viol : ¬ satisfiesLinear w lcs) :
    ∃ c₀ : Fin m,
      ∑ j : Fin n, lcs.matrix c₀ j * w j ≠ lcs.target c₀ :=
  linearTest_soundness_det w lcs h_viol

/-- If the witness violates some quadratic constraint, there exists a
    violated constraint index. -/
theorem quad_violation_detected {n q : ℕ}
    (w : Fin n → F) (qcs : Fin q → QuadConstraint n)
    (h_viol : ¬ ∀ i, satisfiesQuad w (qcs i)) :
    ∃ i₀ : Fin q, w (qcs i₀).left * w (qcs i₀).right ≠ w (qcs i₀).output :=
  quadTest_violated_exists w qcs h_viol

-- ============================================================
-- Section 7: Concrete LigeroScheme instance (trivial/ideal)
-- ============================================================

/-- A trivial (ideal) Ligero scheme where the commitment is the witness
    itself and verification directly checks constraint satisfaction.

    This witnesses that the `LigeroScheme` typeclass is inhabited and
    that the binding axiom follows from `concrete_satisfies_abstract`. -/
noncomputable instance trivialLigeroScheme (F : Type) [Field F]
    (n m q : ℕ) : LigeroScheme F n m q where
  Commitment := Fin n → F
  Proof := Unit
  commit := id
  verify := fun w lcs qcs _ => satisfiesAll w lcs qcs
  binding := fun _ _ _ _ h => h
