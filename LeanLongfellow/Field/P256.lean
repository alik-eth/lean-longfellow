import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Defs
import LeanLongfellow.Field.Pocklington

/-! # Concrete Field Instantiations

Provides `ZMod` instances for the prime fields used by Longfellow (P-256 for
ECDSA) and circom/snarkjs circuits (BN254). -/

/-- The NIST P-256 prime: `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def p256Prime : ℕ :=
  115792089210356248762697446949407573530086143415290314195533631308867097853951

/-- The BN254 prime (alt_bn128 scalar field, used by circom/snarkjs). -/
def bn254Prime : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Primality proofs are in LeanLongfellow.Field.Pocklington, which provides
-- certified Lucas/Pratt certificates via `lucas_primality` from Mathlib.
-- Each proof chains through the complete factorization of `p - 1` with
-- modular-exponentiation witness checks verified by `native_decide`.

instance : Fact (Nat.Prime p256Prime) := Fact.mk p256Prime_prime

instance : Fact (Nat.Prime bn254Prime) := Fact.mk bn254Prime_prime

/-- The P-256 scalar field (NIST curve used by Longfellow for ECDSA). -/
abbrev F_p256 := ZMod p256Prime

/-- The BN254 scalar field (used by circom/snarkjs circuits). -/
abbrev F_bn254 := ZMod bn254Prime

-- Verify that Lean can derive `Field` instances automatically.
example : Field F_p256 := inferInstance
example : Field F_bn254 := inferInstance
