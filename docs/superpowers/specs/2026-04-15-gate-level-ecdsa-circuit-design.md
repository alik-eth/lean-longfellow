# Gate-Level ECDSA Circuit

**Date:** 2026-04-15
**Status:** Approved
**Depends on:** ECDSACircuitSpec (parameterized), ecdsaConstraint_implies_verify, ecScalarMulChain, all sub-problem constraint proofs

## Goal

Replace the coefficient-embedding `ecdsaCircuitSpec` with a real gate-level arithmetic circuit that models the physical GKR topology. The circuit must have non-vacuous extraction (soundness) and completeness.

## Architecture

### Parameters
- `s = 5` (32 wire positions per layer)
- `NL = 12n + 7` layers, where `n` = scalar bit length (256 for P-256)
- One multiplication gate per layer + pass-through add gates
- Public inputs (z, r, s, G, Q, curve params) in layer coefficients
- Private witness (s_inv, u1, u2, bits, intermediates, lambdas) in wire values

### Universal Layer Pattern: `mulPassLayer`

Every layer in the circuit follows the same pattern:
- One mul gate: `mul_poly(out, left, right) = 1`
- Pass-through add gates: `add_poly(p, p, W_ZERO) = 1` for each `p ∈ passthroughs`
- Uncovered positions: forced to 0 by `layerConsistent`

Built via `gatesToLayer` with gate list `[⟨.mul, out, left, right⟩] ++ passthroughs.map (⟨.add, ·, ·, W_ZERO⟩)`.

Some layers use coefficient-based add gates instead of mul gates (for public input multiplication):
- `add_poly(out, src, W_ZERO) = c` where `c` is a field constant (e.g., z, r)
- Gives `V_curr(out) = c * V_next(src)` when `V_next(W_ZERO) = 0`

Core bidirectional lemma:
```
mulPassLayer_iff :
  (∀ g, layerConsistent (mulPassLayer ...) V_curr V_next g) ↔
  V_curr.table out = V_next.table left * V_next.table right ∧
  ∀ p ∈ passthroughs, V_curr.table p = V_next.table p + V_next.table W_ZERO ∧
  ∀ q ∉ ({out} ∪ passthroughs.toFinset), V_curr.table q = 0
```

### Wire Layout (32 positions, static throughout)

```
Pos  Name         Purpose
───────────────────────────────────────
0    W_ZERO       Zero wire (always uncovered)
1    W_SINV       s⁻¹
2    W_U1         u₁ = z · s⁻¹
3    W_U2         u₂ = r · s⁻¹
4    W_ACC_X      Accumulator point x
5    W_ACC_Y      Accumulator point y
6    W_ACC_INF    Accumulator is_inf
7    W_DBL_X      Doubled point x
8    W_DBL_Y      Doubled point y
9    W_DBL_INF    Doubled point is_inf
10   W_PX         Base point x (G or Q)
11   W_PY         Base point y
12   W_BIT        Current scalar bit
13   W_LAMBDA_D   Doubling slope
14   W_LAMBDA_A   Add slope
15   W_TEMP1      Temporary 1 (x², lambda², etc.)
16   W_TEMP2      Temporary 2
17   W_TEMP3      Temporary 3
18   W_P1_X       P₁ result x (= u₁·G)
19   W_P1_Y       P₁ result y
20   W_P1_INF     P₁ is_inf
21   W_P2_X       P₂ result x (= u₂·Q)
22   W_P2_Y       P₂ result y
23   W_P2_INF     P₂ is_inf
24   W_FINAL_X    R.x (final point)
25   W_FINAL_Y    R.y
26   W_FINAL_INF  R.is_inf
27   W_FINAL_LAM  Final addition slope
28   W_TEMP4      Temporary 4
29   W_TEMP5      Temporary 5
30   W_ZCHECK     Zero-wire validation
31   W_OUTPUT     Output (1 if valid)
```

### Layer Sequence

```
Layer indices (0 = output, NL-1 = closest to input):

NL-1 to NL-3    : Phase A — Field ops (3 layers)
                   NL-1: s · s_inv check (mul gate, bottom layer)
                   NL-2: z · s_inv → W_U1 (coeff-add gate)
                   NL-3: r · s_inv → W_U2 (coeff-add gate)

NL-4 to NL-3-6n : Phase B1 — Scalar mul u₁·G (6n layers)
                   Each step = 6 layers:
                   6k+5: acc.x · acc.x → W_TEMP1
                   6k+4: lambda_d · acc.y → W_TEMP2
                   6k+3: lambda_d · lambda_d → W_TEMP3
                   6k+2: lambda_d · (acc.x - dbl.x) → W_TEMP1
                   6k+1: lambda_a · (PX - dbl.x) → W_TEMP2
                   6k+0: lambda_a · lambda_a → W_TEMP3

... to 4         : Phase B2 — Scalar mul u₂·Q (6n layers, same structure)

3 to 1           : Phase C — Point addition P₁+P₂ (3 layers)
                   3: lambda_f · (P2.x - P1.x) → W_TEMP1
                   2: lambda_f² → W_TEMP2
                   1: lambda_f · (P1.x - R.x) → W_TEMP3

0                : Phase D — Equality check (1 layer)
                   (R.x - r)² → W_OUTPUT
```

### Bottom Layer Handling

Layer NL-1 reads from V_NL (unconstrained input). V_NL(W_ZERO) might not be 0.

Solution: Layer NL-1 has its mul gate (s * s_inv) but NO pass-through gates. All positions except the mul output are uncovered (= 0). This establishes V_{NL-1}(W_ZERO) = 0.

Layer NL-2 uses pass-through (safe since V_{NL-1}(W_ZERO) = 0). But it only sees 0s from V_{NL-1} except at the mul output position. So NL-2 must ALSO read from V_{NL-1} directly with its own computation gates.

**Revised bottom approach:** The bottom 3 layers (Phase A) are special — they each have mul/coeff gates reading from the layers below them, building up values progressively. From Phase B onward, all needed witness values are available via pass-through.

Actually, since Phase B needs witness values (bits, intermediates, lambdas) that aren't computed by Phase A, these must come from V_NL through a pass-through chain. The bottom layer breaks this chain.

**Final resolution:** The bottom layer (NL-1) has the mul gate PLUS pass-through gates. The extraction proof handles V_NL(W_ZERO) ≠ 0 by case split:
- If V_NL(W_ZERO) = 0: pass-throughs are exact, proceed normally
- If V_NL(W_ZERO) ≠ 0: pass-throughs are shifted by V_NL(W_ZERO). The mul gate output is still correct (independent of W_ZERO). But shifted pass-through values corrupt subsequent computations. Show that the corrupted output ≠ 1, so extraction holds vacuously.

The "show output ≠ 1 when corrupted" proof: the equality check at layer 0 computes `(R.x - r)²`. When pass-throughs are shifted, all intermediate values carry the offset, and the final check won't produce exactly 1 unless a precise algebraic coincidence occurs. We prove this can't happen by showing the corruption is detectable (the zero-check wire W_ZCHECK carries V_NL(W_ZERO)² through the circuit).

### Extraction Proof Strategy

**Phase 0 — Zero-wire establishment:**
- For k < NL: V_k(W_ZERO) = 0 (uncovered)
- Case split on V_NL(W_ZERO)
- If ≠ 0: show output ≠ 1 via W_ZCHECK propagation
- If = 0: all pass-throughs exact, continue

**Phase A — Field ops extraction:**
```
field_ops_extraction:
  3 layers consistent + V_NL(W_ZERO) = 0 →
  s · V_NL(W_SINV) = V_{NL-1}(W_TEMP1) ∧
  V(W_U1) = z · V_NL(W_SINV) ∧
  V(W_U2) = r · V_NL(W_SINV)
```

**Phase B — Scalar mul extraction (induction on n):**
```
scalar_mul_extraction:
  6n layers consistent + pass-throughs exact →
  ecScalarMulChain params n bits P intermediates doubled lambdas
```
Inductive step: 6 layers verify one doubling + conditional add.

**Phase C — Point add extraction:**
```
point_add_extraction:
  3 layers consistent + pass-throughs exact →
  ecAddFull params P1 P2 R lambda
```

**Phase D — Equality extraction:**
```
equality_extraction:
  layer 0 consistent + V_0.eval target = 1 →
  R.x = r ∧ R.is_inf = 0
```

**Composition:**
Phases A-D → `ecdsaConstraint` → `ecdsaConstraint_implies_verify` → `ecdsaVerify z Q sig`

### Completeness

When `ecdsaVerify z Q sig` holds, construct wire values satisfying all constraints:
- V_NL(W_ZERO) = 0
- V_NL(W_SINV) = s⁻¹
- V_NL(W_BIT_k) = scalar bits of u1 (for chain 1) / u2 (for chain 2)
- V_NL(intermediates, doubled, lambdas) = honest computation
- Show all layers consistent and output = 1

## File Structure

| File | Contents | ~Lines |
|---|---|---|
| `Circuit/GateCircuit.lean` | `mulPassLayer`, `mulPassLayer_iff`, wire position defs, zero-wire lemma | 300 |
| `Circuit/ECDSAGateFieldOps.lean` | Phase A layers + `field_ops_extraction` | 200 |
| `Circuit/ECDSAGateScalarMul.lean` | Phase B layers (inductive) + `scalar_mul_extraction` | 600 |
| `Circuit/ECDSAGatePointAdd.lean` | Phase C layers + `point_add_extraction` | 200 |
| `Circuit/ECDSAGateComposition.lean` | Phase D + zero-wire case split + composition + `ECDSACircuitSpec` + completeness | 300 |

Total: ~1600 lines across 5 new files.

## Dependencies

### From existing codebase (no changes needed)
- `CircuitLayer`, `layerConsistent`, `gatesToLayer`, `gatesToLayer_consistent`
- `single_mul_gate_consistent`, `single_add_gate_consistent`
- `ecdsaConstraint`, `ecdsaConstraint_implies_verify`
- `ecScalarMulChain`, `ecDoubleConstraint`, `ecCondAdd`, `ecAddFull`
- `ECDSACircuitSpec` (parameterized by z, Q, sig)

### From Mathlib
- `Finset.sum_eq_single` — isolating single terms in sums
- `Polynomial.card_roots'` — (already used elsewhere)

## Risk Assessment

**Medium risk:** `mulPassLayer_iff` — proving the bidirectional lemma for a multi-gate layer requires careful `Finset.sum` manipulation with `s = 5` (32-element sums). The single-gate versions exist as reference.

**Medium risk:** Zero-wire case split — showing output ≠ 1 when V_NL(W_ZERO) ≠ 0 requires tracing corruption through the circuit. May need a dedicated lemma about how the offset propagates.

**Low risk:** Phase A, C, D extraction — small fixed number of layers, direct equation extraction.

**Medium risk:** Phase B induction — the inductive step is mechanical (same 6-layer pattern) but matching the `ecScalarMulChain` structure requires careful wire-to-constraint mapping.

**Low risk:** Completeness — constructing honest wire values is straightforward once extraction works.
