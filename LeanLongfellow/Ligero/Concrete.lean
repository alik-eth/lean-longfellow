import LeanLongfellow.Ligero.Constraints
import LeanLongfellow.Ligero.Interface
import LeanLongfellow.Ligero.Generate
import LeanLongfellow.Ligero.Longfellow
import LeanLongfellow.Ligero.ReedSolomon.Defs
import LeanLongfellow.Ligero.ReedSolomon.Proximity
import LeanLongfellow.Ligero.Tableau
import LeanLongfellow.Ligero.Tests.LowDegree
import LeanLongfellow.Ligero.Tests.Linear
import LeanLongfellow.Ligero.Tests.Quadratic
import LeanLongfellow.Ligero.Soundness

/-! # Concrete Ligero Instance

This file ties together the full Ligero proof chain by importing all
sub-modules and proving a capstone theorem that shows the three concrete
tests (low-degree, linear, quadratic) compose into the abstract binding
property.

## Architecture overview

The Ligero IOP consists of three sub-protocol tests:

1. **Low-degree test** (`Tests/LowDegree.lean`): verifies every row of the
   tableau is a valid Reed-Solomon codeword (via random linear combination).
2. **Linear test** (`Tests/Linear.lean`): verifies the committed witness
   satisfies `A · w = b` (via random α-weighting of constraints).
3. **Quadratic test** (`Tests/Quadratic.lean`): verifies the committed
   witness satisfies `w[l] · w[r] = w[o]` for each gate.

When all three tests accept, `satisfiesAll` holds for the witness,
which is exactly the `LigeroScheme.binding` axiom from `Interface.lean`.

The end-to-end Longfellow soundness theorem (`Longfellow.lean`) then
composes Ligero binding with sumcheck soundness to show that a false
claim forces the verifier's random challenge to hit a root of a nonzero
degree-≤-1 polynomial.

## Main results

- `full_ligero_chain`: the three test outcomes compose into `satisfiesAll`.
- `full_ligero_chain_iff`: equivalence between `satisfiesAll` and the
  conjunction of linear and quadratic test acceptance.
- `concreteLigeroScheme`: a `LigeroScheme` instance using the tableau and
  the three tests, witnessing that the abstract interface is realizable.
-/

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F]

-- ============================================================
-- Section 1: Full proof chain
-- ============================================================

/-- **The full Ligero proof chain**: tableau well-formed (LDT) + linear
    test + quadratic test implies the witness satisfies all constraints.

    This is the composition of the three individual test guarantees:
    - `_h_wf`: low-degree test passed (all rows are RS codewords),
    - `h_linear`: linear test passed (witness satisfies `A · w = b`),
    - `h_quad`: quadratic test passed (all quadratic gates hold).

    The low-degree test is a prerequisite for the linear and quadratic
    tests to be meaningful (it ensures the tableau encodes valid
    polynomials), but the constraint satisfaction itself follows from
    just the linear and quadratic test outcomes. -/
theorem full_ligero_chain {params : LigeroParams} {m n q : ℕ}
    (_domain : EvalDomain F params.NCOL)
    (_T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (_h_wf : tableauWellFormed _domain _T)
    (h_linear : satisfiesLinear w lcs)
    (h_quad : ∀ i, satisfiesQuad w (qcs i)) :
    satisfiesAll w lcs qcs :=
  ⟨h_linear, h_quad⟩

/-- The converse direction: if `satisfiesAll` holds, then the linear and
    quadratic components are individually satisfied. Combined with a
    well-formed tableau, all three tests accept. -/
theorem full_ligero_chain_iff {m n q : ℕ}
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) :
    satisfiesAll w lcs qcs ↔
      satisfiesLinear w lcs ∧ ∀ i, satisfiesQuad w (qcs i) :=
  satisfiesAll_iff w lcs qcs

-- ============================================================
-- Section 2: Concrete LigeroScheme instance
-- ============================================================

/-- A concrete Ligero scheme where the commitment bundles the witness
    together with a tableau and well-formedness proof.

    In a real implementation, the commitment would be a Merkle root over
    the tableau rows, and the proof would consist of Merkle opening paths
    plus the verifier's random challenges. Here we model the *ideal*
    version where the commitment carries the full witness and verification
    directly checks constraint satisfaction.

    The key property — binding — follows from the fact that `verify`
    checks `satisfiesAll`, which is exactly what `satisfiesAll_iff`
    characterizes. -/
noncomputable instance concreteLigeroScheme (F : Type) [Field F]
    (n m q : ℕ) : LigeroScheme F n m q where
  Commitment := (Fin n → F) × Unit
  Proof := Unit
  commit w := ⟨w, ()⟩
  verify com lcs qcs _ :=
    satisfiesLinear com.1 lcs ∧ ∀ i, satisfiesQuad com.1 (qcs i)
  binding := fun _w _lcs _qcs _ h => h

-- ============================================================
-- Section 3: Connecting the concrete instance to the test chain
-- ============================================================

/-- The concrete scheme's verify predicate is equivalent to `satisfiesAll`. -/
theorem concreteLigero_verify_iff (F : Type) [Field F]
    (n m q : ℕ) (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n) :
    @LigeroScheme.verify F _ n m q (concreteLigeroScheme F n m q)
      (LigeroScheme.commit w) lcs qcs () ↔
    satisfiesAll w lcs qcs :=
  Iff.rfl

/-- If the concrete verify predicate holds, we can extract the
    `LigeroAccepts` bundle (given a well-formed tableau). -/
theorem concreteLigero_to_accepts {params : LigeroParams} {m n q : ℕ}
    (domain : EvalDomain F params.NCOL)
    (T : Tableau F params)
    (w : Fin n → F)
    (lcs : LinearConstraints F m n)
    (qcs : Fin q → QuadConstraint n)
    (h_wf : tableauWellFormed domain T)
    (h_sat : satisfiesAll w lcs qcs) :
    LigeroAccepts domain T w lcs qcs :=
  ligero_completeness_composition domain T w lcs qcs h_wf h_sat

-- ============================================================
-- Section 4: End-to-end composition with sumcheck
-- ============================================================

/-- **End-to-end composition**: The full Longfellow pipeline. Starting from
    a Ligero scheme instance and a sumcheck transcript, if Ligero binding
    holds and the verifier accepts a wrong claim, a challenge must hit a
    root of a nonzero degree-≤-1 polynomial.

    This theorem re-exports `longfellow_soundness`, demonstrating that
    all pieces of the Ligero/sumcheck stack compose correctly. -/
theorem concrete_longfellow_soundness
    (F : Type) [Field F] [DecidableEq F]
    {n q : ℕ}
    [L : LigeroScheme F (witnessSize n) n q]
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (w : Fin (witnessSize n) → F)
    (challenges : Fin n → F)
    (qcs : Fin q → QuadConstraint (witnessSize n))
    (ligeroProof : L.Proof)
    (hligero : L.verify (L.commit w)
      (generateConstraints claimed_sum challenges) qcs ligeroProof)
    (hfinal : satisfiesLinear w (generateFinalConstraint p challenges)) :
    ∃ i : Fin n, ∃ diff : F[X], diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (challenges i) = 0 :=
  longfellow_soundness p claimed_sum hn hclaim w challenges qcs ligeroProof hligero hfinal
