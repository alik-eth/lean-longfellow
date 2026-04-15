import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Prime.Defs

/-! # Primality Certificates for P-256 and BN254

This module provides certified primality proofs for the two large primes used in
the project — the NIST P-256 prime and the BN254 scalar-field prime — eliminating
the `sorry`'s that previously appeared in `LeanLongfellow.Field.P256`.

## Approach

We use `lucas_primality` from Mathlib (`Mathlib.NumberTheory.LucasPrimality`),
which states: if there exists a witness `a : ZMod p` with `a^(p-1) = 1` and
`a^((p-1)/q) ≠ 1` for every prime factor `q` of `p-1`, then `p` is prime.

Each large prime is proved by providing:
1. The complete factorization of `p - 1`
2. A primitive-root witness `a`
3. `native_decide` checks for the modular-exponentiation conditions

The proof is structured as a bottom-up chain:
- Small primes (≤ 30 bits) are verified directly by `native_decide` on `Nat.Prime`
- Larger primes use `lucas_primality` with recursive certificates for their factors

All modular-exponentiation checks (`a^e mod p`) compile to efficient native code
via `native_decide`, keeping the total verification time under a few seconds.
-/

set_option autoImplicit false

/-! ### Helper lemmas for factorization decomposition -/

/-- If `q` is prime and divides a prime `p`, then `q = p`. -/
private lemma prime_dvd_prime_eq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : q ∣ p) : q = p :=
  (hp.eq_one_or_self_of_dvd q h).resolve_left hq.one_lt.ne'

/-- If `q` is prime and divides `p ^ k` where `p` is prime, then `q = p`. -/
private lemma prime_dvd_prime_pow_eq {p q k : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : q ∣ p ^ k) : q = p :=
  prime_dvd_prime_eq hp hq (hq.dvd_of_dvd_pow h)

/-! ### BN254 primality certificate chain

BN254 scalar-field prime:
  `21888242871839275222246405745257275088548364400416034343698204186575808495617`

Certificate chain (bottom-up):
- 639533339 (30 bits) — base case via `native_decide`
- 65865678001877903 (56 bits) — Lucas certificate, witness 5
- 13818364434197438864469338081 (94 bits) — Lucas certificate, witness 3
- bn254Prime (254 bits) — Lucas certificate, witness 5
-/

/-- 56-bit prime in the BN254 chain.
    `65865678001877902 = 2 * 83 * 379 * 1637 * 639533339` -/
private theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  apply lucas_primality 65865678001877903 (5 : ZMod 65865678001877903)
  · native_decide
  · intro q hq hqd
    have : 65865678001877903 - 1 = 2 * 83 * 379 * 1637 * 639533339 := by native_decide
    rw [this] at hqd
    -- ((((2 * 83) * 379) * 1637) * 639533339)
    rcases hq.dvd_or_dvd hqd with h | h         -- R = 639533339
    · rcases hq.dvd_or_dvd h with h | h          -- R = 1637
      · rcases hq.dvd_or_dvd h with h | h        -- R = 379
        · rcases hq.dvd_or_dvd h with h | h      -- R = 83
          · -- q ∣ 2
            have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
          · -- q ∣ 83
            have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · -- q ∣ 379
          have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 1637
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 639533339
      have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide

/-- 94-bit prime in the BN254 chain.
    `13818364434197438864469338080 = 2^5 * 5 * 823 * 1593227 * 65865678001877903` -/
private theorem prime_13818364434197438864469338081 :
    Nat.Prime 13818364434197438864469338081 := by
  apply lucas_primality 13818364434197438864469338081
    (3 : ZMod 13818364434197438864469338081)
  · native_decide
  · intro q hq hqd
    have : 13818364434197438864469338081 - 1 =
      2 ^ 5 * 5 * 823 * 1593227 * 65865678001877903 := by native_decide
    rw [this] at hqd
    -- ((((2^5 * 5) * 823) * 1593227) * 65865678001877903)
    rcases hq.dvd_or_dvd hqd with h | h           -- R = 65865678001877903
    · rcases hq.dvd_or_dvd h with h | h            -- R = 1593227
      · rcases hq.dvd_or_dvd h with h | h          -- R = 823
        · rcases hq.dvd_or_dvd h with h | h        -- R = 5
          · -- q ∣ 2^5
            have := prime_dvd_prime_pow_eq Nat.prime_two hq h; subst this; native_decide
          · -- q ∣ 5
            have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · -- q ∣ 823
          have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 1593227
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 65865678001877903
      have := prime_dvd_prime_eq prime_65865678001877903 hq h; subst this; native_decide

/-- The BN254 scalar-field prime is prime.
    `bn254Prime - 1 = 2^28 * 3^2 * 13 * 29 * 983 * 11003 * 237073 * 405928799
                       * 1670836401704629 * 13818364434197438864469338081` -/
theorem bn254Prime_prime :
    Nat.Prime 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  apply lucas_primality
    21888242871839275222246405745257275088548364400416034343698204186575808495617
    (5 : ZMod 21888242871839275222246405745257275088548364400416034343698204186575808495617)
  · native_decide
  · intro q hq hqd
    have : 21888242871839275222246405745257275088548364400416034343698204186575808495617
      - 1 = 2 ^ 28 * 3 ^ 2 * 13 * 29 * 983 * 11003 * 237073 * 405928799 *
        1670836401704629 * 13818364434197438864469338081 := by native_decide
    rw [this] at hqd
    -- (((((((((2^28 * 3^2) * 13) * 29) * 983) * 11003) * 237073) * 405928799) * 1670836401704629) * 13818364434197438864469338081)
    rcases hq.dvd_or_dvd hqd with h | h                 -- R = 13818364434197438864469338081
    · rcases hq.dvd_or_dvd h with h | h                  -- R = 1670836401704629
      · rcases hq.dvd_or_dvd h with h | h                -- R = 405928799
        · rcases hq.dvd_or_dvd h with h | h              -- R = 237073
          · rcases hq.dvd_or_dvd h with h | h            -- R = 11003
            · rcases hq.dvd_or_dvd h with h | h          -- R = 983
              · rcases hq.dvd_or_dvd h with h | h        -- R = 29
                · rcases hq.dvd_or_dvd h with h | h      -- R = 13
                  · rcases hq.dvd_or_dvd h with h | h    -- (2^28 * 3^2) split
                    · -- q ∣ 2^28
                      have := prime_dvd_prime_pow_eq Nat.prime_two hq h; subst this; native_decide
                    · -- q ∣ 3^2
                      have := prime_dvd_prime_pow_eq (by native_decide) hq h; subst this; native_decide
                  · -- q ∣ 13
                    have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
                · -- q ∣ 29
                  have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
              · -- q ∣ 983
                have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
            · -- q ∣ 11003
              have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
          · -- q ∣ 237073
            have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · -- q ∣ 405928799
          have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 1670836401704629
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 13818364434197438864469338081
      have := prime_dvd_prime_eq prime_13818364434197438864469338081 hq h
      subst this; native_decide

/-! ### P-256 primality certificate chain

NIST P-256 prime:
  `115792089210356248762697446949407573530086143415290314195533631308867097853951`

Certificate chain (bottom-up):
- 204061199 (28 bits) — Lucas certificate, witness 11
- 34282281433 (35 bits) — Lucas certificate, witness 17
- 66417393611 (36 bits) — Lucas certificate, witness 6
- 11290956913871 (44 bits) — Lucas certificate, witness 13
- 46076956964474543 (56 bits) — Lucas certificate, witness 5
- 774023187263532362759620327192479577272145303 (150 bits) — Lucas certificate, witness 3
- 835945042244614951780389953367877943453916927241 (160 bits) — Lucas certificate, witness 11
- p256Prime (256 bits) — Lucas certificate, witness 6
-/

/-- 28-bit prime in the P-256 chain.
    `204061198 = 2 * 11 * 23 * 107 * 3769` -/
private theorem prime_204061199 : Nat.Prime 204061199 := by
  apply lucas_primality 204061199 (11 : ZMod 204061199)
  · native_decide
  · intro q hq hqd
    have : 204061199 - 1 = 2 * 11 * 23 * 107 * 3769 := by native_decide
    rw [this] at hqd
    -- ((((2 * 11) * 23) * 107) * 3769)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · rcases hq.dvd_or_dvd h with h | h
          · have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
          · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide

/-- 35-bit prime in the P-256 chain.
    `34282281432 = 2^3 * 3 * 7 * 204061199` -/
private theorem prime_34282281433 : Nat.Prime 34282281433 := by
  apply lucas_primality 34282281433 (17 : ZMod 34282281433)
  · native_decide
  · intro q hq hqd
    have : 34282281433 - 1 = 2 ^ 3 * 3 * 7 * 204061199 := by native_decide
    rw [this] at hqd
    -- (((2^3 * 3) * 7) * 204061199)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · -- q ∣ 2^3
          have := prime_dvd_prime_pow_eq Nat.prime_two hq h; subst this; native_decide
        · -- q ∣ 3
          have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 7
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 204061199
      have := prime_dvd_prime_eq prime_204061199 hq h; subst this; native_decide

/-- 36-bit prime in the P-256 chain.
    `66417393610 = 2 * 5 * 53 * 173 * 197 * 3677` -/
private theorem prime_66417393611 : Nat.Prime 66417393611 := by
  apply lucas_primality 66417393611 (6 : ZMod 66417393611)
  · native_decide
  · intro q hq hqd
    have : 66417393611 - 1 = 2 * 5 * 53 * 173 * 197 * 3677 := by native_decide
    rw [this] at hqd
    -- (((((2 * 5) * 53) * 173) * 197) * 3677)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · rcases hq.dvd_or_dvd h with h | h
          · rcases hq.dvd_or_dvd h with h | h
            · have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
            · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
          · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide

/-- 44-bit prime in the P-256 chain.
    `11290956913870 = 2 * 5 * 17 * 66417393611` -/
private theorem prime_11290956913871 : Nat.Prime 11290956913871 := by
  apply lucas_primality 11290956913871 (13 : ZMod 11290956913871)
  · native_decide
  · intro q hq hqd
    have : 11290956913871 - 1 = 2 * 5 * 17 * 66417393611 := by native_decide
    rw [this] at hqd
    -- (((2 * 5) * 17) * 66417393611)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
        · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · have := prime_dvd_prime_eq prime_66417393611 hq h; subst this; native_decide

/-- 56-bit prime in the P-256 chain.
    `46076956964474542 = 2 * 23 * 18169 * 78283 * 704251` -/
private theorem prime_46076956964474543 : Nat.Prime 46076956964474543 := by
  apply lucas_primality 46076956964474543 (5 : ZMod 46076956964474543)
  · native_decide
  · intro q hq hqd
    have : 46076956964474543 - 1 = 2 * 23 * 18169 * 78283 * 704251 := by native_decide
    rw [this] at hqd
    -- ((((2 * 23) * 18169) * 78283) * 704251)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · rcases hq.dvd_or_dvd h with h | h
          · have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
          · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide

/-- 150-bit prime in the P-256 chain.
    `774023187263532362759620327192479577272145302
       = 2 * 3^2 * 2411 * 34282281433 * 11290956913871 * 46076956964474543` -/
private theorem prime_774023187263532362759620327192479577272145303 :
    Nat.Prime 774023187263532362759620327192479577272145303 := by
  apply lucas_primality 774023187263532362759620327192479577272145303
    (3 : ZMod 774023187263532362759620327192479577272145303)
  · native_decide
  · intro q hq hqd
    have : 774023187263532362759620327192479577272145303 - 1 =
      2 * 3 ^ 2 * 2411 * 34282281433 * 11290956913871 * 46076956964474543 := by native_decide
    rw [this] at hqd
    -- (((((2 * 3^2) * 2411) * 34282281433) * 11290956913871) * 46076956964474543)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · rcases hq.dvd_or_dvd h with h | h
          · rcases hq.dvd_or_dvd h with h | h
            · -- q ∣ 2
              have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
            · -- q ∣ 3^2
              have := prime_dvd_prime_pow_eq (by native_decide) hq h; subst this; native_decide
          · -- q ∣ 2411
            have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · -- q ∣ 34282281433
          have := prime_dvd_prime_eq prime_34282281433 hq h; subst this; native_decide
      · -- q ∣ 11290956913871
        have := prime_dvd_prime_eq prime_11290956913871 hq h; subst this; native_decide
    · -- q ∣ 46076956964474543
      have := prime_dvd_prime_eq prime_46076956964474543 hq h; subst this; native_decide

/-- 160-bit prime in the P-256 chain.
    `835945042244614951780389953367877943453916927240
       = 2^3 * 3^3 * 5 * 774023187263532362759620327192479577272145303` -/
private theorem prime_835945042244614951780389953367877943453916927241 :
    Nat.Prime 835945042244614951780389953367877943453916927241 := by
  apply lucas_primality 835945042244614951780389953367877943453916927241
    (11 : ZMod 835945042244614951780389953367877943453916927241)
  · native_decide
  · intro q hq hqd
    have : 835945042244614951780389953367877943453916927241 - 1 =
      2 ^ 3 * 3 ^ 3 * 5 * 774023187263532362759620327192479577272145303 := by native_decide
    rw [this] at hqd
    -- (((2^3 * 3^3) * 5) * 774023187263532362759620327192479577272145303)
    rcases hq.dvd_or_dvd hqd with h | h
    · rcases hq.dvd_or_dvd h with h | h
      · rcases hq.dvd_or_dvd h with h | h
        · -- q ∣ 2^3
          have := prime_dvd_prime_pow_eq Nat.prime_two hq h; subst this; native_decide
        · -- q ∣ 3^3
          have := prime_dvd_prime_pow_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 5
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 774023187263532362759620327192479577272145303
      have := prime_dvd_prime_eq prime_774023187263532362759620327192479577272145303 hq h
      subst this; native_decide

/-- The NIST P-256 prime is prime.
    `p256Prime - 1 = 2 * 3 * 5^2 * 17 * 257 * 641 * 1531 * 65537 * 490463 * 6700417
                     * 835945042244614951780389953367877943453916927241` -/
theorem p256Prime_prime :
    Nat.Prime 115792089210356248762697446949407573530086143415290314195533631308867097853951 := by
  apply lucas_primality
    115792089210356248762697446949407573530086143415290314195533631308867097853951
    (6 : ZMod 115792089210356248762697446949407573530086143415290314195533631308867097853951)
  · native_decide
  · intro q hq hqd
    have : 115792089210356248762697446949407573530086143415290314195533631308867097853951
      - 1 = 2 * 3 * 5 ^ 2 * 17 * 257 * 641 * 1531 * 65537 * 490463 * 6700417 *
        835945042244614951780389953367877943453916927241 := by native_decide
    rw [this] at hqd
    -- ((((((((((2 * 3) * 5^2) * 17) * 257) * 641) * 1531) * 65537) * 490463) * 6700417) * big)
    rcases hq.dvd_or_dvd hqd with h | h                   -- R = big
    · rcases hq.dvd_or_dvd h with h | h                    -- R = 6700417
      · rcases hq.dvd_or_dvd h with h | h                  -- R = 490463
        · rcases hq.dvd_or_dvd h with h | h                -- R = 65537
          · rcases hq.dvd_or_dvd h with h | h              -- R = 1531
            · rcases hq.dvd_or_dvd h with h | h            -- R = 641
              · rcases hq.dvd_or_dvd h with h | h          -- R = 257
                · rcases hq.dvd_or_dvd h with h | h        -- R = 17
                  · rcases hq.dvd_or_dvd h with h | h      -- R = 5^2
                    · rcases hq.dvd_or_dvd h with h | h    -- (2 * 3) split
                      · -- q ∣ 2
                        have := prime_dvd_prime_eq Nat.prime_two hq h; subst this; native_decide
                      · -- q ∣ 3
                        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
                    · -- q ∣ 5^2
                      have := prime_dvd_prime_pow_eq (by native_decide) hq h; subst this; native_decide
                  · -- q ∣ 17
                    have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
                · -- q ∣ 257
                  have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
              · -- q ∣ 641
                have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
            · -- q ∣ 1531
              have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
          · -- q ∣ 65537
            have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
        · -- q ∣ 490463
          have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
      · -- q ∣ 6700417
        have := prime_dvd_prime_eq (by native_decide) hq h; subst this; native_decide
    · -- q ∣ 835945042244614951780389953367877943453916927241
      have := prime_dvd_prime_eq prime_835945042244614951780389953367877943453916927241 hq h
      subst this; native_decide
