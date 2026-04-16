# Tighten EllipticCurve Typeclass Constraints

**Date:** 2026-04-16
**Status:** Approved
**Motivation:** External review identified that end-to-end theorems require only `[EllipticCurve F]`, which has no axioms on `pointAdd`/`scalarMul`. A degenerate instance (e.g., constant `pointAdd`) would make the capstone theorems vacuously true. The existing `EllipticCurveGroup` class adds group laws but is not required by any theorem outside `ScalarMul.lean`.

## Approach

Keep the two-tier class hierarchy (`EllipticCurve` / `EllipticCurveGroup`). Upgrade constraints on all semantically-dependent code from `[EllipticCurve F]` to `[EllipticCurveGroup F]`. Build a new `EllipticCurveGroup` instance for P-256 delegating to Mathlib's `AddCommGroup` on `Point p256WCurve`.

## Change 1: New P-256 `EllipticCurveGroup` Instance

**File:** `LeanLongfellow/Field/P256Curve.lean`
**Location:** After the existing `instance : EllipticCurve F_p256` (line ~101)

```lean
instance : EllipticCurveGroup F_p256 where
  pointAdd_assoc P Q R := add_assoc P Q R
  pointAdd_identity_left P := zero_add P
  pointAdd_identity_right P := add_zero P
  pointAdd_comm P Q := add_comm P Q
```

Each field delegates to Mathlib's `AddCommGroup` on `Point p256WCurve`. The existing `EllipticCurve` instance defines `pointAdd := (· + ·)` and `identity := Point.zero`, so the Mathlib lemmas apply directly.

## Change 2: Constraint Upgrades

Replace `[EllipticCurve F]` with `[EllipticCurveGroup F]` in the following locations:

### Circuit/ECDSA/Spec.lean
- `ecdsaVerify` definition (the core ECDSA verification predicate)
- `ECDSACircuitSpec` structure
- `variable` declaration scoping the extraction theorems

### Circuit/ECDSA/Composition.lean
- All defs and theorems: `ecdsaRecoveryPoint`, `ecdsaVerify_iff`, `ecdsaCoefficient` and variants, `xCoordIndicator`, `ecdsaRealLayer`, `ecdsaCircuitSpec`, `ecdsaCircuitSpec_complete`, `ecdsaCircuitSpec_sound`, `ecdsaComposition_longfellow_soundness`

### Circuit/ECDSA/GateComposition.lean
- `coeffOutputLayer`, `coeffOutputLayer_iff`, `ecdsaGateLayers`, `ecdsaGateCircuitSpec`

### Circuit/ECDSA/Circuit.lean
- `CurveInstantiation` class definition

### Circuit/EC/ScalarMul.lean (correctness theorems only)
- `scalarMulChain_invariant`, `scalarMulChain_matches_doubleAndAdd`, `scalarMulChain_correct`, `scalarMulChain_invariant_explicit`

**Not changed in ScalarMul.lean:** `doubleAndAdd` (def), `doubleAndAdd_zero`, `doubleAndAdd_succ` — these are purely structural and legitimately need only `[EllipticCurve F]`.

### EndToEnd.lean
- `ZkEidasProof`, `zkEidasVerifierAccepts`
- `zkEidas_soundness_det`, `zkEidas_no_root_implies_valid`
- `zkEidas_predicate_binding`, `zkEidas_escrow_integrity`, `zkEidas_nullifier_binding`, `zkEidas_holder_binding`
- `zkEidas_full_soundness`, `zkEidas_full_soundness_or_collision`
- `ZkEidasFullProof`, `zkEidasFullVerify`
- `zkEidasFull_soundness`, `zkEidasFull_soundness_or_collision`

## What Does NOT Change

- `EllipticCurve` class definition (Spec.lean) — stays as-is
- `EllipticCurveGroup` class definition (ScalarMul.lean) — stays as-is
- `doubleAndAdd` and its two unfolding lemmas — structural only
- `nsmulEC` and related theorems — already on `[EllipticCurveGroup F]`
- `P256CurveInstantiation.lean` — inherits the upgrade via `CurveInstantiation`
- `ProbabilisticLongfellow.lean` — operates at Ligero/sumcheck level, no EC constraint

## Proof Impact

No proof modifications expected. Rationale:

1. `EllipticCurveGroup extends EllipticCurve` — all field accesses resolve through the parent.
2. No existing proof exploits the *absence* of group laws. Strengthening a hypothesis cannot break a proof.
3. P-256 typeclass resolution: `[EllipticCurveGroup F_p256]` implies `[EllipticCurve F_p256]`, so downstream code expecting the base class resolves automatically.

## Verification

`lake build` must succeed after all changes. Any failure would indicate an accidental dependency on the weaker constraint worth investigating independently.

## Outcome

The capstone `zkEidas_full_soundness_or_collision [EllipticCurveGroup F]` can no longer be instantiated with degenerate curve arithmetic. Any instance must prove associativity, commutativity, and identity laws. For P-256, Mathlib discharges these.
