# Degree-d Sumcheck Generalization

**Date:** 2026-04-14
**Status:** Approved
**Depends on:** Sumcheck (complete), Fiat-Shamir (complete)
**Sub-project of:** Longfellow degree-2 gap closure (A of A/B/C)

## Motivation

The current formalization hardcodes degree ≤ 1 for sumcheck round polynomials. Longfellow's combining polynomial `Q·V·V` produces degree-2 round polynomials. The soundness argument (Schwartz-Zippel) generalizes cleanly: a nonzero degree-≤-d polynomial has at most d roots, giving error bound `d·n/|F|` instead of `n/|F|`.

This sub-project generalizes the sumcheck soundness and Fiat-Shamir layers to degree ≤ d, unblocking the circuit model (sub-project B) and concrete Ligero (sub-project C).

## Key Design Decisions

1. **`SumcheckRound` and `verifierAccepts` are unchanged.** The verifier still checks `p(0) + p(1) = target` — the Boolean hypercube sum doesn't change with degree. Degree is a soundness concern, not a verification condition.

2. **Degree bound is a hypothesis, not a structural parameter.** `hdeg : ∀ i, (rounds i).prover_poly.natDegree ≤ d` is passed to soundness theorems. No new type parameters on `SumcheckRound`.

3. **Witness encoding stays at 2 per round.** `witnessSize n = 2 * n` is unchanged. `decodeRounds` produces degree-≤-1 polynomials via `polyFromEvals`. The Ligero/Longfellow layer stays as-is — it inherently operates at degree ≤ 1 through the 2-point encoding. When sub-project B adds `d+1` point encoding, Longfellow.lean will naturally pick up degree ≤ d.

4. **Drop custom Schwartz-Zippel lemma.** `roots_le_one_of_deg_le_one` is deleted. Replaced by direct use of Mathlib's `Polynomial.card_roots' : p.roots.card ≤ p.natDegree`.

## File Changes

### Modified Files

#### `Sumcheck/Soundness.lean`

**Delete:** `roots_le_one_of_deg_le_one` — replaced by Mathlib's `Polynomial.card_roots'`.

**Generalize:** `sumcheck_soundness_det` — add implicit `{d : ℕ}`, change `≤ 1` → `≤ d`:

```lean
theorem sumcheck_soundness_det {n : ℕ} {d : ℕ} (p : MultilinearPoly F n) (claimed_sum : F)
    (rounds : Fin n → SumcheckRound F)
    (hn : 0 < n)
    (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (haccept : verifierAccepts p claimed_sum rounds)
    (hdeg : ∀ i : Fin n, (rounds i).prover_poly.natDegree ≤ d) :
    ∃ i : Fin n, ∃ (diff : F[X]), diff ≠ 0 ∧ diff.natDegree ≤ d ∧
      diff.eval (rounds i).challenge = 0
```

The `1 ≤ d` hypothesis is needed because the honest prover has degree ≤ 1, so `diff = adversary - honest` has degree ≤ `max(d, 1)`. With `1 ≤ d`, this simplifies to `≤ d`. In practice, Longfellow uses `d = 2`.

Proof structure is identical. The inductive argument propagates a wrong claim through rounds — it never uses the degree value, only passes it through. The degree bound on `diff` comes from `natDegree_sub_le` and the hypotheses, plus `hd` to ensure `max(d, 1) = d`.

**Generalize:** `sumcheck_soundness_concrete` — same treatment, add `{d : ℕ}` and `(hd : 1 ≤ d)`, change `≤ 1` → `≤ d`.

#### `FiatShamir/Oracle.lean`

**Generalize:** `countSat_adaptive_root` — add `{d : ℕ}`, bound becomes `d * |F|^(n-1)`:

```lean
theorem countSat_adaptive_root {n : ℕ} {d : ℕ} (i : Fin n)
    (D : RandomChallenges F n → Polynomial F)
    (hD_indep : ∀ cs cs', (∀ j, j ≠ i → cs j = cs' j) → D cs = D cs')
    (hD_deg : ∀ cs, (D cs).natDegree ≤ d) :
    countSat (fun cs => D cs ≠ 0 ∧ (D cs).eval (cs i) = 0) ≤
      d * Fintype.card F ^ (n - 1)
```

**New proof strategy (fiber counting):** The current proof uses injectivity (two satisfying `cs` agreeing on non-`i` coords must agree on `i` because degree ≤ 1 means at most 1 root). This breaks for d > 1.

New approach:
1. Partition `Fin n → F` into fibers by the `n-1` non-`i` coordinates. There are `|F|^(n-1)` fibers.
2. Within each fiber, `D` is constant by `hD_indep` (all coords except `i` are fixed).
3. If `D = 0` in a fiber, the `D cs ≠ 0` condition fails — 0 satisfying elements.
4. If `D ≠ 0` in a fiber, `D.eval (cs i) = 0` has at most `d` solutions by `Polynomial.card_roots'` and `hD_deg`.
5. Total: at most `d` per fiber × `|F|^(n-1)` fibers = `d * |F|^(n-1)`.

In Lean, this is implemented by:
- Using `Fin.insertNthEquiv` to biject `Fin n → F` with `F × (Fin (n-1) → F)`
- Summing over fibers using `Finset.sum` / `Finset.biUnion`
- Within each fiber, bounding by `d` using `card_roots'`

**Generalize:** `countSat_root_hit` — add `{d : ℕ}`, bound becomes `d * |F|^(n-1)`:

```lean
theorem countSat_root_hit {n : ℕ} {d : ℕ} (i : Fin n)
    {p : Polynomial F} (hp : p ≠ 0) (hdeg : p.natDegree ≤ d) :
    countSat (fun cs : RandomChallenges F n => p.eval (cs i) = 0) ≤
      d * Fintype.card F ^ (n - 1)
```

Proof adapts directly: the `d.roots.toFinset.card ≤ 1` step becomes `≤ d` via `card_roots'` and `hdeg`.

#### `FiatShamir/Soundness.lean`

**Generalize:** `fiatShamir_soundness` — add `{d : ℕ}`, bound becomes `n * (d * |F|^(n-1))`:

```lean
theorem fiatShamir_soundness {n : ℕ} {d : ℕ}
    (p : MultilinearPoly F n) (claimed_sum : F)
    (hn : 0 < n)
    (hd : 1 ≤ d)
    (hclaim : claimed_sum ≠ ∑ b : Fin n → Bool, p.table b)
    (adversary : RandomChallenges F n → FiatShamirProof F n)
    (hdeg : ∀ cs i, ((adversary cs).round_polys i).natDegree ≤ d)
    (h_nonadaptive : ∀ (cs cs' : RandomChallenges F n) (i : Fin n),
      (∀ j : Fin n, j.val < i.val → cs j = cs' j) →
      (adversary cs).round_polys i = (adversary cs').round_polys i) :
    countSat (fun cs => fsVerifierAccepts p claimed_sum (adversary cs) cs) ≤
      n * (d * Fintype.card F ^ (n - 1))
```

Proof structure identical:
1. `sumcheck_soundness_concrete` (now with `d` and `hd`) gives witness round with degree-≤-d diff
2. Union bound over n rounds
3. Per-round: `countSat_adaptive_root` (now with `d`) gives `≤ d * |F|^(n-1)`

`honestProver_poly_indep` is unchanged — it doesn't mention degree.

### Unchanged Files (12)

- `MLE/Defs.lean`, `MLE/Eval.lean`, `MLE/Extension.lean`, `MLE/Props.lean`
- `Sumcheck/Protocol.lean`, `Sumcheck/Completeness.lean`
- `FiatShamir/Transform.lean`
- `Ligero/Constraints.lean`, `Ligero/Interface.lean`, `Ligero/Generate.lean`, `Ligero/Longfellow.lean`
- `Field/Basic.lean`

## Backward Compatibility

All existing call sites use degree ≤ 1. After generalization, they instantiate `d = 1` and get the same bounds. No breaking changes — `d` is implicit and inferred from the `hdeg` hypothesis.

The honest prover (`honestProver_deg_le`) still proves degree ≤ 1, so completeness is unaffected.

## Risk Assessment

**Low risk:** `sumcheck_soundness_det`, `sumcheck_soundness_concrete`, `fiatShamir_soundness` — mechanical `1` → `d` substitution, proof structure unchanged.

**Medium risk:** `countSat_adaptive_root` — requires a fundamentally different proof (fiber counting vs. injectivity). The math is standard but the Lean encoding needs careful `Finset`/`Fintype` bookkeeping with `Fin.insertNthEquiv`.

**No new sorry's expected.** The fiber-counting proof for `countSat_adaptive_root` is concrete and all building blocks exist in Mathlib.

## Dependencies

### From Mathlib (already imported)
- `Polynomial.card_roots'` — `p.roots.card ≤ p.natDegree`
- `Fin.insertNthEquiv` — bijection `(α i) × (∀ j, α (i.succAbove j)) ≃ (∀ j, α j)`
- `Finset.card_biUnion_le` — for union bound in fiber counting

### From existing codebase (no changes needed)
- `verifierAccepts`, `SumcheckRound`, `honestProver` — Protocol.lean
- `honestProver_deg_le`, `sumFirstVar_natDegree_le` — used in degree bounds
- `countSat`, `countSat_union_bound`, `countSat_eq_val` — Oracle.lean

## Non-Goals

- Changing `verifierAccepts` or `SumcheckRound`
- Adding circuit model or combining polynomial (sub-project B)
- Changing witness encoding to `d+1` per round (sub-project B)
- Concrete Ligero internals (sub-project C)
- Specific instantiation at `d = 2`
