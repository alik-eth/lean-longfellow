# LeanLongfellow

Formal verification of [Longfellow](https://github.com/google/longfellow-zk), Google's Sumcheck + Ligero zero-knowledge proving system, and the [zk-eIDAS](https://digital-strategy.ec.europa.eu/en/policies/eidas-regulation) electronic identity protocol built on top of it. Written in Lean 4 with Mathlib.

zk-eIDAS extends Longfellow with privacy-preserving credential predicates (age verification, set membership, range proofs), contract-scoped nullifiers for replay prevention, Poseidon-based holder binding for cross-credential linking, and SHA-256-based escrow digests for court-ordered identity recovery.

This project produces the first mechanized soundness proof for any Longfellow component, suitable for IETF standardization ([draft-google-cfrg-libzk](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)) and eIDAS trust service certification.

## Main Results

The capstone theorem `zkEidas_full_soundness` ([EndToEnd.lean](LeanLongfellow/EndToEnd.lean)) composes all five security properties into a single conjunction:

1. **ECDSA soundness** — if no sumcheck challenge hits a polynomial root, the ECDSA signature is valid (from GKR composition + Schwartz-Zippel)
2. **Predicate binding** — any alternative claim matching the same Poseidon commitment satisfies the predicate (from collision resistance, non-trivially via commitment binding)
3. **Escrow integrity** — the authority can recover the original fields from the escrow digest (from CRHash collision resistance)
4. **Nullifier binding** — same nullifier implies same credential, contract, and salt (from Poseidon collision resistance)
5. **Holder binding** — same holder hash implies same holder identity (from Poseidon collision resistance)

The underlying proof chain builds on sumcheck soundness, GKR circuit composition, Ligero binding, and Fiat-Shamir probability bounds (`n * d / |F|`).

All theorems (590+) are machine-checked by Lean 4's kernel. The soundness chain contains **zero** `sorry`, `admit`, or `axiom` statements. Primality of the P-256 and BN254 primes is proven via Pocklington certificates with `native_decide`.

```
$ lake env lean -c 'import LeanLongfellow.EndToEnd; #print axioms zkEidas_full_soundness'
'zkEidas_full_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The only axioms are Lean's three kernel axioms — no domain-specific trusted assumptions.

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```sh
# Install elan (if not already installed)
curl https://elan-init.trycloudflare.com/ -sSf | sh

# Build
lake build
```

Lean version is pinned in `lean-toolchain` to `leanprover/lean4:v4.30.0-rc1`. Mathlib is fetched automatically by Lake. First build takes ~5 minutes with cached Mathlib oleans.

## Project Structure

```
LeanLongfellow/
├── MLE/                    # Multilinear polynomial representation
│   ├── Defs.lean           # MultilinearPoly: (Fin n → Bool) → F
│   ├── Eval.lean           # Evaluation and partial evaluation
│   ├── Extension.lean      # MLE uniqueness theorem
│   └── Props.lean          # Degree bounds, interpolation
│
├── Sumcheck/               # Interactive sumcheck protocol
│   ├── Protocol.lean       # Prover/verifier messages, honest prover
│   ├── Completeness.lean   # Honest prover is always accepted
│   ├── Soundness.lean      # Wrong claim => root hit (Schwartz-Zippel)
│   └── Pad.lean            # HVZK simulator construction
│
├── FiatShamir/             # Fiat-Shamir (random oracle model)
│   ├── Oracle.lean         # RandomChallenges, countSat, union bound
│   ├── Transform.lean      # Interactive-to-non-interactive transform
│   └── Soundness.lean      # Probability bound: n*d / |F|
│
├── Ligero/                 # Ligero commitment scheme
│   ├── Interface.lean      # Abstract LigeroScheme typeclass
│   ├── Constraints.lean    # Linear/quadratic constraint system
│   ├── Generate.lean       # Sumcheck -> constraint encoding
│   ├── Longfellow.lean     # End-to-end Ligero soundness
│   ├── Soundness.lean      # Binding from three tests
│   ├── Concrete.lean       # Concrete instantiation
│   ├── FiatShamir.lean     # Non-interactive Ligero
│   ├── ProbabilisticBinding.lean # Single-challenge soundness (error ≤ 2/|F|)
│   ├── ProbabilisticE2E.lean # Error bound composition
│   ├── Tableau.lean        # Matrix tableau representation
│   ├── MerkleCommitment.lean # Merkle-based commitment
│   ├── ReedSolomon/        # Reed-Solomon proximity testing
│   │   ├── Defs.lean
│   │   ├── Distance.lean
│   │   └── Proximity.lean
│   └── Tests/              # Ligero sub-protocol tests
│       ├── Linear.lean
│       ├── Quadratic.lean
│       └── LowDegree.lean
│
├── Circuit/                # Arithmetic circuit model (GKR)
│   ├── Defs.lean           # CircuitLayer, LayerValues, consistency
│   ├── EqPoly.lean         # Lagrange basis / equality polynomial
│   ├── Combining.lean      # Combining polynomial for add/mul gates
│   ├── Reduction.lean      # Per-layer sumcheck reduction
│   ├── Composition.lean    # Multi-layer GKR composition
│   ├── Probability.lean    # Circuit-level probability bounds
│   ├── GateCircuit.lean    # Gate-level circuit construction
│   ├── Gates.lean          # Gate-level definitions and proofs
│   ├── WireFormat.lean     # Wire indexing
│   ├── WireFormatSpec.lean # Wire format specification
│   ├── Examples.lean       # Small circuit examples
│   ├── Gadgets.lean        # Reusable circuit gadgets
│   ├── GadgetGates.lean    # Gadget-to-gate compilation
│   ├── ECArith.lean        # Elliptic curve arithmetic constraints
│   ├── CurveInstantiation.lean # Abstract EC-to-circuit bridge typeclass
│   ├── ECBridge.lean       # Abstract-to-circuit EC bridge
│   ├── ECDSA.lean          # ECDSA verification spec (parameterized)
│   ├── ECDSACircuit.lean   # Constraint-level ECDSA verification
│   ├── ECDSAComposition.lean # Non-vacuous circuit extraction + completeness
│   ├── ECDSAFieldOps.lean  # Field op circuit layers
│   ├── ECDSAPointOps.lean  # Point addition circuit layers
│   ├── ECDSAEqualityCheck.lean # Equality check circuit layer
│   ├── P256CurveInstantiation.lean # Concrete P-256 CurveInstantiation
│   ├── ScalarMul.lean      # Scalar multiplication chain correctness
│   ├── Word32.lean         # 32-bit word arithmetic in field
│   ├── SHA256.lean         # SHA-256 compression constraints
│   ├── SHA256NIST.lean     # NIST FIPS 180-4 concrete constants
│   ├── SHA256Round.lean    # SHA-256 per-round constraints
│   ├── SHA256Sound.lean    # SHA-256 circuit determinism
│   └── SHA256Spec.lean     # SHA-256 specification theorems
│
├── Poseidon/               # Poseidon hash (commitment layer)
│   ├── Defs.lean           # PoseidonHash typeclass (CR as explicit hyp)
│   ├── Concrete.lean       # PoseidonSponge bridge
│   ├── Nullifier.lean      # Nullifier binding and replay prevention
│   └── HolderBinding.lean  # Holder identity binding
│
├── Predicate/              # Credential predicate logic
│   ├── Defs.lean           # PredicateSpec, predicateHolds
│   └── Correctness.lean    # Predicate soundness
│
├── Escrow/                 # Key escrow for authority recovery
│   ├── Defs.lean           # CRHash, EscrowFields, commitments
│   ├── Correctness.lean    # Escrow integrity theorem
│   └── SHA256Bridge.lean   # SHA-256 circuit => CRHash instance
│
├── Merkle/                 # Merkle tree commitments
│   ├── Defs.lean           # MerkleHash typeclass, tree/path types
│   └── Correctness.lean    # Binding and path verification
│
├── ZeroKnowledge/          # Honest-verifier zero-knowledge
│   ├── Defs.lean           # HVZK definitions, simulator type
│   └── HVZK.lean           # Sumcheck HVZK theorem
│
├── Field/                  # Finite field instantiations
│   ├── Basic.lean          # ZMod 97 (test field)
│   ├── P256.lean           # P-256 and BN254 prime declarations
│   ├── P256Curve.lean      # Concrete P-256 EllipticCurve instance
│   ├── Pocklington.lean    # Pocklington primality certificates
│   └── Subfield.lean       # GF(2^16) → GF(2^128) embedding
│
└── EndToEnd.lean           # Capstone: zkEidas_full_soundness
```

## Proof Chain

The formalization is structured as a layered composition. Each layer's conclusions discharge the hypotheses of the layer above.

```
                    zkEidas_full_soundness
                            |
            +---------------+---------------+
            |               |               |
   zkEidas_soundness_det    |    zkEidas_predicate_soundness
            |               |               |
  ecdsa_longfellow_soundness|    predicateCommitment_binding
            |               |               |
     gkr_composition        |       (CR hypothesis)
            |               |
  layer_reduction_soundness |    zkEidas_escrow_integrity
            |               |               |
   sumcheck_soundness_det   |       escrow_integrity
            |               |               |
   (Schwartz-Zippel)        |    CRHash.collision_resistant
                            |
                 fiatShamir_soundness
                            |
              countSat_union_bound + countSat_adaptive_root
```

## Cryptographic Assumptions

The formalization is parametric over standard cryptographic primitives, encoded as Lean typeclasses:

| Assumption | Typeclass | Property | Status |
|---|---|---|---|
| Poseidon collision resistance | `PoseidonHash` | Explicit `hcr` hypothesis on binding theorems | Hypothesis |
| Elliptic curve operations | `EllipticCurve` | Abstract group law | Instantiated (P-256) |
| Merkle hash collision resistance | `MerkleHash` | `Function.Injective hash2` | Hypothesis |
| Ligero binding | `LigeroScheme` | `verify(commit w) => satisfiesAll w` | Proven (three-test) |
| Generic collision resistance | `CRHash` | `Function.Injective hash` | Hypothesis |
| SHA-256 constants | `SHA256Constants` | NIST FIPS 180-4 round constants | Instantiated |
| EC circuit agreement | `CurveInstantiation` | Abstract ops match circuit constraints | Instantiated (P-256) |
| P-256 / BN254 primality | `Fact (Nat.Prime p)` | Field characteristic is prime | Proven (Pocklington) |
| P-256 curve nonsingularity | — | Generator on curve, discriminant ≠ 0 | Proven (`native_decide`) |

Collision resistance for Poseidon, Merkle, and CRHash is modeled as an explicit `Function.Injective` hypothesis on theorems that need it, rather than a typeclass field. This avoids the unsatisfiable `(Fin n → F) → F` injectivity for finite fields while keeping the assumption visible and auditable.

## Known Limitations

- **Zero `sorry`s and zero `axiom`s** in the codebase. All primality proofs use Pocklington certificates verified by `native_decide`. All curve properties use `native_decide` over `ZMod`.
- **Collision resistance is modeled as injectivity (`Function.Injective`).** This is the standard approach in symbolic/algebraic formal verification, as Lean does not model computational complexity. However, for finite fields the hypotheses `Function.Injective (F^n -> F)` are **unsatisfiable by cardinality** when `n >= 2` (pigeonhole): there is no injective function from a larger set to a smaller one. Consequently, the binding theorems that assume hash injectivity (predicate binding, nullifier binding, holder binding, escrow integrity) hold vacuously for any concrete finite field instantiation. This is a known limitation shared by all symbolic-model formalizations. A computational model (PPT adversaries, negligible advantage) would address this but requires axiomatizing complexity theory, which is beyond the scope of current proof assistants. Collision resistance appears as an explicit hypothesis (`hcr : Function.Injective ...`) on theorems that need it, not as a typeclass field, keeping the assumption visible and auditable.
- **ECDSA circuit extraction** uses a coefficient-embedding technique (encoding the verification predicate in `add_poly`) rather than a gate-by-gate arithmetic circuit. This is mathematically sound and proves both soundness and completeness, but does not model the physical circuit topology of a real GKR implementation.

## Design Decisions

**Custom MLE representation.** Multilinear polynomials are represented as evaluation tables `(Fin n -> Bool) -> F` rather than using Mathlib's `MvPolynomial`. This mirrors how Longfellow actually uses MLEs and avoids coercing `MvPolynomial` into a multilinear shape. The approach follows the Isabelle AFP sumcheck proof (CSF 2024, Garvia Bosshard et al.).

**Typeclass-based crypto assumptions.** Cryptographic primitives are axiomatized as typeclasses rather than standalone axioms. This makes assumptions explicit in theorem signatures and allows concrete instantiation (e.g., `LigeroScheme` has two concrete instances).

**Deterministic-first, then probability.** The core soundness chain is deterministic ("wrong claim => root hit"). Probability bounds are composed separately via `fiatShamir_soundness` and `longfellow_total_error`, keeping the algebraic core clean.

## Future Directions

**Backend-agnostic eIDAS verification.** The current formalization verifies zk-eIDAS over Longfellow (Sumcheck + Ligero). However, many of the security properties — predicate soundness, nullifier binding, escrow integrity, holder binding — are independent of the proving system. A natural next step is to abstract over the ZK backend via a generic `ZKProofSystem` typeclass, then instantiate it for both Longfellow and Groth16 (the original zk-eIDAS Circom implementation). This would prove that eIDAS security properties hold regardless of which ZK backend is used, as long as the backend satisfies basic soundness. The predicate, escrow, and Poseidon modules are already backend-agnostic; the remaining work is abstracting the circuit-to-ZK bridge.

## References

- [IETF draft-google-cfrg-libzk](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/) — Longfellow protocol specification
- [Ligero: Lightweight Sublinear Arguments Without a Trusted Setup](https://eprint.iacr.org/2022/1608) (Ames et al., CCS 2017)
- [Proofs, Arguments, and Zero-Knowledge](https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.html) (Thaler, 2022) — GKR and sumcheck reference
- [Sumcheck protocol formalization in Isabelle](https://www.isa-afp.org/entries/Sumcheck_Protocol.html) (Garvia Bosshard et al., CSF 2024)
- [eIDAS 2.0 Regulation](https://digital-strategy.ec.europa.eu/en/policies/eidas-regulation) — EU electronic identity framework

## License

See [LICENSE](LICENSE).
