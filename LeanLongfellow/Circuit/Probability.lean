import LeanLongfellow.Circuit.Composition
import LeanLongfellow.FiatShamir.Soundness

open Finset Polynomial MultilinearPoly Classical

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-! # GKR Probabilistic Soundness

Connects the deterministic GKR composition theorem (`gkr_composition`) to
concrete probability bounds via the Fiat-Shamir counting infrastructure.

## Error analysis

Each circuit layer runs a sumcheck with `2*s` rounds over a degree-≤-2
combining polynomial. By `fiatShamir_soundness` with `d = 2` and `n = 2*s`,
a single layer's sumcheck accepts a wrong claim on at most
`(2*s) * (2 * |F|^(2*s - 1))` out of `|F|^(2*s)` challenge vectors, giving
per-layer error probability `2*s * 2 / |F|`.

For `NL` layers the challenges are independent. By a union bound the total
error probability is at most `NL * 2*s * 2 / |F|`.

## What is formalised here

1. **`total_gkr_rounds`** — total sumcheck rounds across all layers.
2. **`layer_error_bound`** — per-layer counting bound, instantiating
   `fiatShamir_soundness` with `d = 2`.
3. A docstring stating the multi-layer union bound.  Formally proving it
   would require a product-space `countSat` that we have not yet built;
   the per-layer bound is the load-bearing formal statement.
-/

/-- Total number of sumcheck rounds across all NL layers of a GKR proof,
    each layer having `2*s` rounds. -/
def total_gkr_rounds (NL s : ℕ) : ℕ := NL * (2 * s)

/-- **Per-layer probabilistic soundness.**

For a single circuit layer with `2*s` sumcheck rounds and a degree-≤-2
adversary, the number of challenge vectors that make the verifier accept
a wrong claim is at most `(2*s) * (2 * |F|^(2*s - 1))`.

This is `fiatShamir_soundness` instantiated with `d = 2` and `n = 2*s`.
Dividing by `|F|^(2*s)` gives probability ≤ `2*s * 2 / |F|`. -/
theorem layer_error_bound {s : ℕ}
    (p : MultilinearPoly F (2 * s)) (claimed_sum : F)
    (hs : 0 < 2 * s)
    (hclaim : claimed_sum ≠ ∑ b : Fin (2 * s) → Bool, p.table b)
    (adversary : RandomChallenges F (2 * s) → FiatShamirProof F (2 * s))
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ 2)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F (2 * s)) (i : Fin (2 * s)),
      (∀ j : Fin (2 * s), j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      (2 * s) * (2 * Fintype.card F ^ (2 * s - 1)) :=
  fiatShamir_soundness p claimed_sum hs (by omega) hclaim adversary hdeg h_nonadaptive

/-! ### Multi-layer error bound (informal)

**Theorem** (multi-layer GKR soundness). *For an NL-layer arithmetic circuit
with gates of fan-in 2 and `s`-bit layer width, the probability that a
cheating prover convinces the GKR verifier of a wrong output claim is at
most*

$$\Pr[\text{accept} \mid \text{wrong claim}] \;\le\; \frac{NL \cdot 2s \cdot 2}{|F|}.$$

**Proof sketch.**
1. `gkr_composition` shows deterministically that if the output claim is
   wrong and every layer's sumcheck verifier accepts, then some challenge
   hit a root of a nonzero degree-≤-2 polynomial at some layer/round.
2. `layer_error_bound` bounds each layer's contribution: at most
   `(2*s) * 2 / |F|` of the challenge space causes acceptance.
3. The challenges for distinct layers are independent, so the probability
   that *any* layer's bad event occurs is bounded by the sum of the
   individual probabilities (union bound), giving `NL * (2*s) * 2 / |F|`.

The per-layer bound (step 2) is formally proved above. The product-space
union bound (step 3) would require lifting `countSat` to a product of
per-layer challenge spaces; we leave this as future work and record the
bound here for reference. -/

end
