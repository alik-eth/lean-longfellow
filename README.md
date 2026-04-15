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

A strictly stronger variant `zkEidas_full_soundness_or_collision` removes all hash injectivity hypotheses. Its conclusion is a disjunction: either all five properties hold, or a concrete collision witness can be extracted for Poseidon-3, Poseidon-1, or CRHash. This makes the theorem **non-vacuous for finite fields**, where `Function.Injective (F^n → F)` is unsatisfiable by cardinality.

The underlying proof chain builds on sumcheck soundness, GKR multi-layer composition, Ligero binding (with Merkle commitment), Fiat-Shamir hash-derived soundness in the Random Oracle Model, and probabilistic error bounds (`≤ 2/|F|` for Ligero, `n·d/|F|` for sumcheck).

All theorems (710+) are machine-checked by Lean 4's kernel. The soundness chain contains **zero** `sorry`, `admit`, or `axiom` statements. Primality of the P-256 and BN254 primes is proven via Pocklington certificates with `native_decide`.

```
$ lake env lean -c 'import LeanLongfellow.EndToEnd; #print axioms zkEidas_full_soundness_or_collision'
'zkEidas_full_soundness_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
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
│   ├── Soundness.lean      # Probability bound: n*d / |F|
│   └── HashDerived.lean    # Hash-derived challenges, ROM reduction
│
├── Ligero/                 # Ligero commitment scheme
│   ├── Interface.lean      # Abstract LigeroScheme typeclass
│   ├── Constraints.lean    # Linear/quadratic constraint system
│   ├── Generate.lean       # Sumcheck -> constraint encoding
│   ├── Longfellow.lean     # End-to-end Ligero soundness
│   ├── Soundness.lean      # Binding from three tests
│   ├── Concrete.lean       # Concrete instantiation
│   ├── FiatShamir.lean     # Non-interactive Ligero (single-challenge)
│   ├── ProbabilisticBinding.lean # Probabilistic binding (error ≤ 2/|F|)
│   ├── ProbabilisticE2E.lean # Error bound composition (union bound)
│   ├── ProbabilisticLongfellow.lean # niLigero → deterministic soundness bridge
│   ├── Tableau.lean        # Matrix tableau representation
│   ├── MerkleCommitment.lean # Column hash commitment (CR as explicit hyp)
│   ├── MerkleLigeroScheme.lean # LigeroScheme instance with Merkle commitment
│   ├── ReedSolomon/        # Reed-Solomon proximity testing
│   │   ├── Defs.lean
│   │   ├── Decode.lean     # RS decoding + knowledge extractability
│   │   ├── ConcreteDomain.lean
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
│   ├── GateCircuit.lean    # Gate-level circuit infrastructure (s=5, 32 wires)
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
│   ├── ECDSAComposition.lean # Abstract circuit extraction + completeness
│   ├── ECDSAFieldOps.lean  # Abstract field op circuit layers
│   ├── ECDSAPointOps.lean  # Abstract point addition circuit layers
│   ├── ECDSAEqualityCheck.lean # Equality check circuit layer
│   ├── ECDSAGateFieldOps.lean  # Gate-level field ops (Phase A, 3 layers)
│   ├── ECDSAGateScalarMul.lean # Gate-level scalar mul (Phase B, 7 layers/step)
│   ├── ECDSAGatePointAdd.lean  # Gate-level point add (Phase C, 3 layers)
│   ├── ECDSAGateComposition.lean # Gate-level composition (14n+7 layers)
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
│   ├── Defs.lean           # PoseidonHash typeclass, collision types
│   ├── Concrete.lean       # PoseidonSponge bridge
│   ├── Nullifier.lean      # Nullifier binding (+ _or_collision)
│   └── HolderBinding.lean  # Holder identity binding (+ _or_collision)
│
├── Predicate/              # Credential predicate logic
│   ├── Defs.lean           # PredicateSpec, predicateHolds
│   └── Correctness.lean    # Predicate soundness
│
├── Escrow/                 # Key escrow for authority recovery
│   ├── Defs.lean           # CRHash typeclass, collision types
│   ├── Correctness.lean    # Escrow integrity (+ _or_collision)
│   └── SHA256Bridge.lean   # SHA-256 circuit => CRHash instance
│
├── Merkle/                 # Merkle tree commitments
│   ├── Defs.lean           # MerkleHash typeclass, collision types
│   ├── Concrete.lean       # Poseidon-based MerkleHash/ColumnHash
│   └── Correctness.lean    # Binding (+ _or_collision)
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
              zkEidas_full_soundness_or_collision
                            |
      +----------+----------+----------+----------+
      |          |          |          |          |
    ECDSA    Predicate   Escrow    Nullifier  Holder
      |          |          |          |          |
      |    commitment   integrity  binding    binding
      |    _or_collision _or_coll  _or_coll  _or_coll
      |          |          |          |          |
      |      (Poseidon   (CRHash  (Poseidon  (Poseidon
      |       hash)       hash)    hash)      hash)
      |
  longfellow_soundness ← generateAllConstraints
      |
  gkr_chain_soundness (genuine multi-layer induction)
      |
  layer_reduction_soundness
      |                    Probabilistic layer:
  sumcheck_soundness_det   niLigero_binding_or_bad
      |                         |
  (Schwartz-Zippel)        error ≤ 2/|F|
                                |
                    fiatShamir_hash_soundness
                                |
                 deriveChallenges + ROM reduction
                                |
                 countSat_union_bound + countSat_adaptive_root
```

## Cryptographic Assumptions

The formalization is parametric over standard cryptographic primitives, encoded as Lean typeclasses:

| Assumption | Typeclass | Property | Status |
|---|---|---|---|
| Poseidon collision resistance | `PoseidonHash` | Explicit `hcr` hypothesis or `_or_collision` | Non-vacuous |
| Elliptic curve operations | `EllipticCurve` | Abstract group law | Instantiated (P-256) |
| Merkle hash collision resistance | `MerkleHash` | Explicit hypothesis or `_or_collision` | Non-vacuous |
| Column hash collision resistance | `ColumnHash` | Explicit hypothesis or `_or_collision` | Non-vacuous |
| Generic collision resistance | `CRHash` | Explicit hypothesis or `_or_collision` | Non-vacuous |
| Ligero binding | `LigeroScheme` | `verify(commit w) => satisfiesAll w` | Proven (three-test + Merkle) |
| Random oracle | `RandomOracle` | Hash-derived challenges in ROM | Reduced to random |
| SHA-256 constants | `SHA256Constants` | NIST FIPS 180-4 round constants | Instantiated |
| EC circuit agreement | `CurveInstantiation` | Abstract ops match circuit constraints | Instantiated (P-256) |
| P-256 / BN254 primality | `Fact (Nat.Prime p)` | Field characteristic is prime | Proven (Pocklington) |
| P-256 curve nonsingularity | — | Generator on curve, discriminant ≠ 0 | Proven (`native_decide`) |

**No hash typeclass has injectivity as a class field.** Collision resistance is handled in two complementary ways:

1. **Explicit hypothesis** — theorems like `predicateCommitment_binding` take `Function.Injective hash` as an argument, keeping the assumption visible and auditable.
2. **Collision-extracting reductions** — theorems like `predicateCommitment_binding_or_collision` require no injectivity hypothesis. The conclusion is: binding holds OR a concrete collision witness can be extracted. This is **non-vacuous for finite fields**, where the injectivity hypothesis is unsatisfiable by cardinality.

## Known Limitations

- **Zero `sorry`s and zero `axiom`s** in the codebase. All primality proofs use Pocklington certificates verified by `native_decide`. All curve properties use `native_decide` over `ZMod`.
- **Symbolic collision resistance model.** Lean does not model computational complexity, so collision resistance is expressed as injectivity (`Function.Injective`) or collision extraction (`binding ∨ collision`). A computational model (PPT adversaries, negligible advantage) would be strictly stronger but requires axiomatizing complexity theory, which is beyond current proof assistants. The collision-extracting reductions ensure all binding theorems are non-vacuous for finite fields.
- **SHA-256 escrow bridge covers the single-block case** (8 × 32 bits = 256 bits). The multi-block case (8 × 32 bytes = 256 bytes, requiring 5 SHA-256 blocks) is documented but not formalized.

## Design Decisions

**Custom MLE representation.** Multilinear polynomials are represented as evaluation tables `(Fin n -> Bool) -> F` rather than using Mathlib's `MvPolynomial`. This mirrors how Longfellow actually uses MLEs and avoids coercing `MvPolynomial` into a multilinear shape. The approach follows the Isabelle AFP sumcheck proof (CSF 2024, Garvia Bosshard et al.).

**Typeclass-based crypto assumptions.** Cryptographic primitives are axiomatized as typeclasses rather than standalone axioms. This makes assumptions explicit in theorem signatures and allows concrete instantiation (e.g., `LigeroScheme` has two concrete instances).

**Deterministic-first, then probability.** The core soundness chain is deterministic ("wrong claim => root hit"). Probability bounds are composed separately via `fiatShamir_hash_soundness` and `longfellow_total_error`, keeping the algebraic core clean. The probabilistic layer bridges single-challenge Ligero verification (`niLigeroVerify`) to the deterministic soundness conclusion via `ProbabilisticLongfellow.lean`.

**Two-tier ECDSA circuit.** The ECDSA verification circuit has both an abstract and a gate-level formalization. The abstract tier (`ECDSAComposition.lean`) encodes the verification predicate as a polynomial coefficient for clean extraction proofs. The gate-level tier (`ECDSAGate*.lean`, 1500+ lines) models the physical circuit with `mulPassLayer` gates across 14n+7 layers. Both produce `ECDSACircuitSpec` instances with non-vacuous extraction.

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
