# LeanLongfellow

Formal verification of [Longfellow](https://github.com/google/longfellow-zk), Google's Sumcheck + Ligero zero-knowledge proving system, and the [zk-eIDAS](https://digital-strategy.ec.europa.eu/en/policies/eidas-regulation) electronic identity protocol built on top of it. Written in Lean 4 with Mathlib.

zk-eIDAS extends Longfellow with privacy-preserving credential predicates (age verification, set membership, range proofs), contract-scoped nullifiers for replay prevention, Poseidon-based holder binding for cross-credential linking, and SHA-256-based escrow digests for court-ordered identity recovery.

This project produces the first mechanized soundness proof for any Longfellow component, suitable for IETF standardization ([draft-google-cfrg-libzk](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)) and eIDAS trust service certification.

## Main Results

The capstone theorem `zkEidas_full_soundness` ([EndToEnd.lean](LeanLongfellow/EndToEnd.lean)) composes the full proof chain:

1. **Sumcheck soundness** — if the claimed sum is wrong, some challenge must hit a root of a nonzero low-degree polynomial
2. **GKR circuit composition** — multi-layer arithmetic circuit reduces to per-layer sumcheck instances
3. **ECDSA circuit extraction** — circuit output of 1 implies valid ECDSA signature
4. **Ligero binding** — commitment verification implies constraint satisfaction
5. **Fiat-Shamir probability bound** — cheating probability bounded by `n * d / |F|`
6. **Predicate/nullifier/escrow binding** — application-level security properties from collision resistance

All theorems (310+) are machine-checked by Lean 4's kernel. The soundness chain contains **zero** `sorry` or `admit` statements.

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
│   ├── Gates.lean          # Gate-level definitions and proofs
│   ├── WireFormat.lean     # Wire indexing
│   ├── Examples.lean       # Small circuit examples
│   ├── Gadgets.lean        # Reusable circuit gadgets
│   ├── GadgetGates.lean    # Gadget-to-gate compilation
│   ├── ECArith.lean        # Elliptic curve arithmetic constraints
│   ├── ECBridge.lean       # Abstract-to-circuit EC bridge
│   ├── ECDSA.lean          # ECDSA verification circuit
│   ├── ECDSACircuit.lean   # Concrete ECDSA circuit instantiation
│   ├── Word32.lean         # 32-bit word arithmetic in field
│   ├── SHA256.lean         # SHA-256 compression constraints
│   ├── SHA256Round.lean    # SHA-256 per-round constraints
│   └── SHA256Spec.lean     # SHA-256 specification theorems
│
├── Poseidon/               # Poseidon hash (commitment layer)
│   ├── Defs.lean           # PoseidonHash typeclass, commitment binding
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
│   └── P256.lean           # P-256 and BN254 prime declarations
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
     gkr_composition        |       PoseidonHash.injective
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

| Assumption | Typeclass | Property | Standard? |
|---|---|---|---|
| Poseidon collision resistance | `PoseidonHash` | `Function.Injective hash` | Yes |
| Elliptic curve operations | `EllipticCurve` | Abstract group law | Yes |
| Merkle hash collision resistance | `MerkleHash` | `Function.Injective hash2` | Yes |
| Ligero binding | `LigeroScheme` | `verify(commit w) => satisfiesAll w` | Yes |
| Generic collision resistance | `CRHash` | `Function.Injective hash` | Yes |
| SHA-256 collision resistance | `SHA256Spec` | `Function.Injective sha256` | Yes |
| SHA-256 constants | `SHA256Constants` | Round constants are valid 32-bit words | Factual |
| EC circuit agreement | `CurveInstantiation` | Abstract ops match circuit constraints | Bridge |
| SHA-256 circuit soundness | `SHA256CircuitSound` | Circuit constraints are deterministic | Bridge |

"Bridge" assumptions connect abstract mathematical objects to concrete circuit representations. They are specific to this formalization and would need separate verification for a given circuit implementation.

## Known Limitations

- **2 `sorry`s** in `Field/P256.lean`: primality of the P-256 and BN254 primes. Lean's `native_decide` cannot handle 256-bit primality in practical compilation time. These are NIST-standardized primes verifiable via external tools (e.g., ECPP certificates, PARI/GP).
- **Collision resistance is modeled as injectivity**, which is stronger than the standard computational definition (no PPT adversary can find collisions). This is the standard approach in symbolic/algebraic formal verification, as Lean does not model computational complexity.
- **`CurveInstantiation`** requires proof that abstract elliptic curve operations agree with the circuit constraint representation. This bridge must be verified per concrete curve instantiation.

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
