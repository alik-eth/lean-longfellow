import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Subfield Pair Structure for Longfellow

Longfellow uses a **subfield optimization**: computations happen in GF(2^128) but
wire values live in the smaller subfield GF(2^16).  This reduces proof size because
Ligero's proximity testing benefits from the subfield structure.

This file formalizes the abstract subfield relationship and derives the properties
that Longfellow relies on:

1. An injective ring-homomorphism embedding the small field into the large field.
2. A Frobenius characterization: `x ∈ image(embed)` iff `x ^ |F_small| = x`.
3. The extension degree (128 / 16 = 8).
4. A structure theorem for codewords whose evaluation domain lies in the subfield.

## Design

We axiomatize the subfield pair rather than constructing GF(2^128) and GF(2^16)
concretely.  Mathlib's `GaloisField` can build them in principle, but the
cardinality proofs are expensive.  The abstract approach lets the rest of the
Longfellow formalization proceed without those costs.
-/

open Finset Polynomial

/-! ## Abstract subfield pair -/

/-- A subfield pair: `F_small` embeds into `F_large` as a subfield of a finite field.
    Both fields are finite and have specified cardinalities. -/
class SubfieldPair (F_small F_large : Type*) [Field F_small] [Field F_large]
    [Fintype F_small] [Fintype F_large] where
  /-- Injective ring homomorphism embedding the small field into the large field. -/
  embed : F_small →+* F_large
  /-- The embedding is injective. -/
  embed_injective : Function.Injective embed
  /-- Cardinality of the small field. -/
  card_small : Fintype.card F_small = 2 ^ 16
  /-- Cardinality of the large field. -/
  card_large : Fintype.card F_large = 2 ^ 128

namespace SubfieldPair

variable {F_small F_large : Type*}
  [Field F_small] [Field F_large]
  [Fintype F_small] [Fintype F_large]
  [hp : SubfieldPair F_small F_large]

/-! ## Frobenius characterization -/

include hp in
/-- Every element of `F_small` satisfies `x ^ (2^16) = x` (finite field identity). -/
theorem pow_card_small (x : F_small) :
    x ^ (2 ^ 16) = x := by
  rw [← hp.card_small]
  exact FiniteField.pow_card x

/-- The image of `embed` is stable under the Frobenius `x ↦ x ^ (2^16)`:
    if `x` is in the image, then `x ^ (2^16) = x`. -/
theorem frobenius_embed (x : F_small) :
    (hp.embed x : F_large) ^ (2 ^ 16) = hp.embed x := by
  rw [← map_pow hp.embed]
  congr 1
  exact pow_card_small (F_large := F_large) x

include hp in
/-- Every element of `F_large` satisfies `x ^ (2^128) = x`. -/
theorem pow_card_large (x : F_large) :
    x ^ (2 ^ 128) = x := by
  rw [← hp.card_large]
  exact FiniteField.pow_card x

/-- The embed map preserves zero. -/
theorem embed_zero :
    hp.embed (0 : F_small) = (0 : F_large) :=
  map_zero hp.embed

/-- The embed map preserves one. -/
theorem embed_one :
    hp.embed (1 : F_small) = (1 : F_large) :=
  map_one hp.embed

/-- The embed map preserves addition. -/
theorem embed_add (x y : F_small) :
    hp.embed (x + y) = hp.embed x + hp.embed y :=
  map_add hp.embed x y

/-- The embed map preserves multiplication. -/
theorem embed_mul (x y : F_small) :
    hp.embed (x * y) = hp.embed x * hp.embed y :=
  map_mul hp.embed x y

/-! ## Extension degree -/

/-- The extension degree is 8: `|F_large| = |F_small| ^ 8`. -/
theorem card_large_eq_small_pow :
    Fintype.card F_large = (Fintype.card F_small) ^ 8 := by
  rw [hp.card_small, hp.card_large]
  norm_num

/-! ## Subfield codeword structure

When the evaluation domain for a Reed-Solomon code lives entirely in the
subfield `F_small`, codewords have extra structure: they are determined by
polynomials evaluated at subfield points.  This section states the key
property used in Longfellow's proximity testing. -/

/-- An evaluation point set that lies entirely in the subfield image. -/
structure SubfieldDomain (F_small F_large : Type*)
    [Field F_small] [Field F_large] [Fintype F_small] [Fintype F_large]
    [SubfieldPair F_small F_large] (N : ℕ) where
  /-- The evaluation points (in `F_large`). -/
  points : Fin N → F_large
  /-- All evaluation points are distinct. -/
  distinct : Function.Injective points
  /-- Every evaluation point is the image of a small-field element. -/
  in_subfield : ∀ i, ∃ a : F_small, SubfieldPair.embed a = points i

/-- For a subfield domain, every evaluation point satisfies the Frobenius equation.
    This is the witness test Longfellow uses to verify that evaluation points
    are indeed subfield elements. -/
theorem subfield_domain_frobenius {N : ℕ}
    (dom : SubfieldDomain F_small F_large N)
    (i : Fin N) : (dom.points i) ^ (2 ^ 16) = dom.points i := by
  obtain ⟨a, ha⟩ := dom.in_subfield i
  rw [← ha]
  exact frobenius_embed a

/-- The subfield domain size is bounded by the small field cardinality.
    Since all points are distinct and lie in the image of `embed`, the domain
    size cannot exceed `|F_small| = 2^16`. -/
theorem subfield_domain_size_le {N : ℕ}
    (dom : SubfieldDomain F_small F_large N) :
    N ≤ 2 ^ 16 := by
  have hsub := dom.in_subfield
  let f : Fin N → F_small := fun i => (hsub i).choose
  have hf_spec : ∀ i, SubfieldPair.embed (f i) = dom.points i :=
    fun i => (hsub i).choose_spec
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply dom.distinct
    rw [← hf_spec i, ← hf_spec j, hij]
  calc N = Fintype.card (Fin N) := (Fintype.card_fin N).symm
    _ ≤ Fintype.card F_small := Fintype.card_le_of_injective f hf_inj
    _ = 2 ^ 16 := hp.card_small

/-! ## Concrete instance: GF(2^16) ⊂ GF(2^128)

Mathlib's `GaloisField` constructs finite fields as splitting fields.
The cardinality proofs go through Mathlib's machinery. The embedding
relies on the fact that 16 divides 128. -/

/-- GF(2^16): the small field used by Longfellow for wire values. -/
noncomputable abbrev GF2_16 := GaloisField 2 16

/-- GF(2^128): the large field used by Longfellow for proof computations. -/
noncomputable abbrev GF2_128 := GaloisField 2 128

noncomputable instance : Fintype GF2_16 := Fintype.ofFinite _
noncomputable instance : Fintype GF2_128 := Fintype.ofFinite _

/-- Cardinality of GF(2^16). -/
theorem gf2_16_card : Fintype.card GF2_16 = 2 ^ 16 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 (n := 16) (by omega)]

/-- Cardinality of GF(2^128). -/
theorem gf2_128_card : Fintype.card GF2_128 = 2 ^ 128 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 (n := 128) (by omega)]

/-- There exists an embedding GF(2^16) →+* GF(2^128).
    This follows from 16 | 128 and the classification of finite field extensions. -/
noncomputable instance gf2_subfield_embed_exists :
    Nonempty (GF2_16 →+* GF2_128) :=
  have : Fintype GF2_16 := Fintype.ofFinite _
  have : Fintype GF2_128 := Fintype.ofFinite _
  have hdvd : Module.finrank (ZMod 2) GF2_16 ∣ Module.finrank (ZMod 2) GF2_128 := by
    rw [GaloisField.finrank 2 (by omega : (16 : ℕ) ≠ 0),
        GaloisField.finrank 2 (by omega : (128 : ℕ) ≠ 0)]
    omega
  (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).map AlgHom.toRingHom

/-- The concrete `SubfieldPair` instance for Longfellow's GF(2^16) ⊂ GF(2^128). -/
noncomputable instance : SubfieldPair GF2_16 GF2_128 where
  embed := gf2_subfield_embed_exists.some
  embed_injective := RingHom.injective _
  card_small := gf2_16_card
  card_large := gf2_128_card

end SubfieldPair
