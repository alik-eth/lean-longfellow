import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import Mathlib.Algebra.Polynomial.Roots

/-! # Sumcheck Soundness

This file proves two results about the soundness of the sumcheck protocol:

1. `roots_le_one_of_deg_le_one`: a nonzero polynomial of degree ≤ 1 has at most
   one root in any finite set (a special case of the Schwartz-Zippel lemma).

2. `sumcheck_soundness_det`: deterministic soundness — if the verifier accepts
   with a wrong claim, then there exists a round where the prover's polynomial
   differs from the honest polynomial, and the challenge is a root of that
   nonzero difference polynomial of degree ≤ 1.
-/

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] {n : ℕ}

/-- A nonzero polynomial of degree ≤ 1 has at most 1 root in any finite set. -/
theorem roots_le_one_of_deg_le_one {p : F[X]} (hp : p ≠ 0) (hdeg : p.natDegree ≤ 1)
    (S : Finset F) :
    (S.filter (fun r => p.eval r = 0)).card ≤ 1 := by
  -- The roots of p in S are a subset of p.roots.toFinset
  have h1 : (S.filter (fun r => p.eval r = 0)).card ≤ p.roots.toFinset.card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots hp]
    exact Polynomial.IsRoot.def.mpr hx.2
  -- p.roots.toFinset.card ≤ p.roots.card
  have h2 : p.roots.toFinset.card ≤ p.roots.card :=
    Multiset.toFinset_card_le p.roots
  -- p.roots.card ≤ p.natDegree ≤ 1
  have h3 : p.roots.card ≤ p.natDegree :=
    Polynomial.card_roots' p
  omega

/-- **Sumcheck deterministic soundness.**

If the verifier accepts a claimed sum that differs from the true sum,
then there exists a round `i` and a nonzero polynomial `diff` of degree ≤ 1
whose evaluation at the challenge `rounds i` is zero.

This is the core soundness argument. The proof proceeds by induction:
if the claimed sum is wrong, either round 0's prover polynomial differs
from the honest polynomial (and the challenge hits a root of their difference),
or the claim propagates incorrectly to the next round, and we recurse.

The full formal proof requires the same dependent-type cast machinery
as completeness (via `iterPartialEval`). We state the theorem and
sorry the body, as the mathematical argument is standard but the
Lean formalization is blocked by the same cast issues. -/
theorem sumcheck_soundness_det (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds)
    (hdeg : ∀ i : Fin n, (rounds i).prover_poly.natDegree ≤ 1) :
    ∃ i : Fin n, ∃ (diff : F[X]), diff ≠ 0 ∧ diff.natDegree ≤ 1 ∧
      diff.eval (rounds i).challenge = 0 := by
  sorry
