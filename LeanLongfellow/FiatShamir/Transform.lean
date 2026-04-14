import LeanLongfellow.Sumcheck.Protocol
import LeanLongfellow.Sumcheck.Completeness
import LeanLongfellow.FiatShamir.Oracle

open Finset Polynomial MultilinearPoly

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n : ℕ}

/-- A non-interactive sumcheck proof: the round polynomials. -/
structure FiatShamirProof (F : Type*) [Field F] (n : ℕ) where
  round_polys : Fin n → Polynomial F

/-- Reconstruct interactive rounds from a proof and random challenges. -/
def toRounds (proof : FiatShamirProof F n) (cs : RandomChallenges F n) :
    Fin n → SumcheckRound F :=
  fun i => ⟨proof.round_polys i, cs i⟩

/-- Non-interactive verifier: derive challenges, run interactive verifier. -/
def fsVerifierAccepts (p : MultilinearPoly F n) (claimed_sum : F)
    (proof : FiatShamirProof F n) (cs : RandomChallenges F n) : Prop :=
  verifierAccepts p claimed_sum (toRounds proof cs)

/-- Extract a FiatShamirProof from the honest interactive prover. -/
noncomputable def fsHonestProof (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    FiatShamirProof F n where
  round_polys i := (honestProver p cs i).prover_poly

omit [DecidableEq F] [Fintype F] in
/-- Definitional unfolding of `fsVerifierAccepts`. -/
theorem fsVerifierAccepts_iff (p : MultilinearPoly F n) (claimed_sum : F)
    (proof : FiatShamirProof F n) (cs : RandomChallenges F n) :
    fsVerifierAccepts p claimed_sum proof cs ↔
      verifierAccepts p claimed_sum (toRounds proof cs) := Iff.rfl

omit [DecidableEq F] [Fintype F] in
/-- The challenge of the honest prover at round `i` equals `cs i`. -/
theorem honestProver_challenge {n : ℕ} (p : MultilinearPoly F n) (cs : Fin n → F) (i : Fin n) :
    (honestProver p cs i).challenge = cs i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [honestProver_zero]
    · simp only [honestProver_succ]
      exact ih (p.partialEvalFirst (cs 0)) (fun k => cs k.succ) j

omit [DecidableEq F] [Fintype F] in
/-- The honest FS proof reconstructs the honest interactive rounds. -/
theorem toRounds_fsHonest (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    toRounds (fsHonestProof p cs) cs = honestProver p cs := by
  funext i
  simp only [toRounds, fsHonestProof]
  -- Goal: ⟨(honestProver p cs i).prover_poly, cs i⟩ = honestProver p cs i
  rw [← honestProver_challenge p cs i]

omit [DecidableEq F] [Fintype F] in
/-- **Fiat-Shamir completeness:** the honest FS prover is always accepted. -/
theorem fiatShamir_completeness (p : MultilinearPoly F n) (cs : RandomChallenges F n) :
    fsVerifierAccepts p (∑ b : Fin n → Bool, p.table b) (fsHonestProof p cs) cs := by
  unfold fsVerifierAccepts
  rw [toRounds_fsHonest]
  exact sumcheck_completeness p cs
