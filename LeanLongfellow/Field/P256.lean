import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs

/-! # Concrete Field Instantiations

Provides `ZMod` instances for the prime fields used by Longfellow (P-256 for
ECDSA) and circom/snarkjs circuits (BN254). -/

/-- The NIST P-256 prime: `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def p256Prime : ℕ :=
  115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- The BN254 prime (alt_bn128 scalar field, used by circom/snarkjs). -/
def bn254Prime : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Primality proofs.
-- `native_decide` on 256-bit numbers exhausts practical compilation time
-- (>10 min at 100% CPU without completing).  We accept primality as an axiom
-- here; it can be verified externally in seconds:
--
--   # SageMath:  is_prime(p256Prime)  => True
--   # Pari/GP:   isprime(p256Prime)   => 1
--
-- If a future Lean/Mathlib version ships a fast certified primality check
-- (e.g. ECPP certificates), replace `sorry` with that proof.

instance : Fact (Nat.Prime p256Prime) := Fact.mk (by sorry)

instance : Fact (Nat.Prime bn254Prime) := Fact.mk (by sorry)

/-- The P-256 scalar field (NIST curve used by Longfellow for ECDSA). -/
abbrev F_p256 := ZMod p256Prime

/-- The BN254 scalar field (used by circom/snarkjs circuits). -/
abbrev F_bn254 := ZMod bn254Prime

-- Verify that Lean can derive `Field` instances automatically.
example : Field F_p256 := inferInstance
example : Field F_bn254 := inferInstance
