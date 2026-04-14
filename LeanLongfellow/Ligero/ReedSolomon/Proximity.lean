import LeanLongfellow.Ligero.ReedSolomon.Defs
import LeanLongfellow.Ligero.ReedSolomon.Distance
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Reed-Solomon Proximity Testing

This file establishes proximity testing results for Reed-Solomon codes.

The core property of RS codes used for proximity testing is the *minimum distance*:
any two distinct codewords disagree on at least `N - k + 1` positions. This means
that opening a few random positions is very likely to detect the difference between
a corrupted word and any valid codeword.

## Main theorems

- `rs_codewords_agree_k_implies_eq`: two codewords agreeing on at least `k` positions
  must be identical.
- `rs_recovery`: if a word agrees with a codeword on at least `k` positions, then
  either they are equal or the word is not a codeword.
- `rs_min_distance`: any two distinct codewords disagree on at least `N - k + 1` positions.
- `proximity_detection_single`: counting bound for single-position detection.
- `proximity_detection_multi_bad_bound`: multi-position detection bound.
-/

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Agreement forces equality for codewords -/

/-- If two codewords agree on at least `k` positions, they must be identical.
    This follows directly from `rs_agreement_bound`: two distinct codewords can
    agree on at most `k - 1` positions, so agreement on at least `k` is a contradiction. -/
theorem rs_codewords_agree_k_implies_eq {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (h_agree : k ≤ (Finset.univ.filter (fun i => w₁ i = w₂ i)).card) :
    w₁ = w₂ := by
  by_contra hne
  have hbound := rs_agreement_bound domain k hk w₁ w₂ hw₁ hw₂ hne
  -- hbound : card ≤ k - 1, h_agree : k ≤ card
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- k = 0: both codewords are evaluations of the zero polynomial
    exfalso; apply hne
    obtain ⟨c₁, rfl⟩ := hw₁
    obtain ⟨c₂, rfl⟩ := hw₂
    funext i
    simp [rsEncode]
  · -- k > 0: card ≤ k - 1 and k ≤ card gives k ≤ k - 1, contradiction
    omega

/-- If a word agrees with a codeword on at least `k` positions, then either the word
    equals the codeword or the word is not itself a codeword.

    This is the fundamental recovery/proximity principle: a codeword is uniquely
    determined among all codewords by its values at any `k` positions. -/
theorem rs_recovery {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (word cw : Fin N → F)
    (h_cw : isRSCodeword domain k cw)
    (h_agree : k ≤ (Finset.univ.filter (fun i => word i = cw i)).card) :
    word = cw ∨ ¬isRSCodeword domain k word := by
  by_contra h
  push Not at h
  obtain ⟨hne, hw⟩ := h
  exact absurd (rs_codewords_agree_k_implies_eq domain k hk word cw hw h_cw h_agree) hne

/-! ### Minimum distance -/

/-- The Hamming distance filter: positions where two words differ. -/
abbrev hammingDiffSet {N : ℕ} (w₁ w₂ : Fin N → F) : Finset (Fin N) :=
  Finset.univ.filter (fun i => w₁ i ≠ w₂ i)

omit [Field F] in
/-- The agreement and disagreement sets partition `Finset.univ`. -/
theorem agree_disagree_card {N : ℕ} (w₁ w₂ : Fin N → F) :
    (Finset.univ.filter (fun i => w₁ i = w₂ i)).card +
    (hammingDiffSet w₁ w₂).card = N := by
  have hpart : Finset.univ.filter (fun i : Fin N => w₁ i = w₂ i) ∪
               Finset.univ.filter (fun i : Fin N => w₁ i ≠ w₂ i) = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdisj : Disjoint (Finset.univ.filter (fun i : Fin N => w₁ i = w₂ i))
                         (Finset.univ.filter (fun i : Fin N => w₁ i ≠ w₂ i)) := by
    apply Finset.disjoint_filter.mpr
    intro i _ h1 h2
    exact absurd h1 h2
  rw [← Finset.card_union_of_disjoint hdisj, hpart, Finset.card_univ, Fintype.card_fin]

/-- Two distinct RS codewords disagree on at least `N - k + 1` positions.
    This is the minimum distance of the RS code. -/
theorem rs_min_distance {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂) :
    N - k + 1 ≤ (hammingDiffSet w₁ w₂).card := by
  have hagree := rs_agreement_bound domain k hk w₁ w₂ hw₁ hw₂ hne
  have htotal := agree_disagree_card w₁ w₂
  -- From htotal: diff_card = N - agree_card
  -- From hagree: agree_card ≤ k - 1
  -- So diff_card ≥ N - (k - 1) = N - k + 1
  -- We prove it via: N - k + 1 + agree_card ≤ diff_card + agree_card = N
  -- i.e., N - k + 1 ≤ N - agree_card
  -- Since agree_card ≤ k - 1 and k ≤ N.
  -- Handle k = 0 separately (vacuous: all k=0 codewords are the zero function)
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso; apply hne
    obtain ⟨c₁, rfl⟩ := hw₁
    obtain ⟨c₂, rfl⟩ := hw₂
    funext i; simp [rsEncode]
  · -- k > 0. Goal: N - k + 1 ≤ diff_card
    -- We have: agree_card ≤ k - 1 and agree_card + diff_card = N
    -- First establish N - k + 1 = N - (k - 1) for k > 0, k ≤ N
    have hrewrite : N - k + 1 = N - (k - 1) := by omega
    rw [hrewrite]
    -- Goal: N - (k - 1) ≤ diff_card
    -- diff_card = N - agree_card (from htotal)
    have hdiff : (hammingDiffSet w₁ w₂).card =
        N - (Finset.univ.filter (fun i => w₁ i = w₂ i)).card := by omega
    rw [hdiff]
    -- Goal: N - (k - 1) ≤ N - agree_card
    exact Nat.sub_le_sub_left hagree N

/-! ### Proximity detection bounds -/

/-- **Single-position detection (counting bound)**: if two codewords are distinct,
    opening any single position detects the difference for at least `N - k + 1`
    out of `N` possible positions.

    As a probability statement (not formalized): a uniformly random position
    detects the difference with probability at least `(N - k + 1) / N`. -/
theorem proximity_detection_single {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂) :
    N - k + 1 ≤ (hammingDiffSet w₁ w₂).card :=
  rs_min_distance domain k hk w₁ w₂ hw₁ hw₂ hne

/-- The fraction of detecting positions restated as a cross-multiplication
    to avoid division: `(N - k + 1) * 1 ≤ diffCard * 1`. -/
theorem proximity_fraction {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂) :
    (N - k + 1) * N ≤ (hammingDiffSet w₁ w₂).card * N := by
  exact Nat.mul_le_mul_right N (rs_min_distance domain k hk w₁ w₂ hw₁ hw₂ hne)

/-! ### Multi-position detection -/

/-- **Multi-position detection (counting bound)**: if two codewords differ on
    at least `N - k + 1` positions, then a `t`-tuple of positions (with
    replacement) that ALL agree is "bad". The number of such bad tuples is
    at most `(k - 1) ^ t`.

    A `t`-tuple of positions is a function `Fin t -> Fin N`. A tuple is "bad"
    if at every opened position the two words agree. Since each position in a
    bad tuple must land in the agreement set (which has at most `k - 1` elements),
    the number of bad tuples is at most `(k - 1) ^ t`. -/
theorem proximity_detection_multi_bad_bound {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ) (hk : k ≤ N)
    (w₁ w₂ : Fin N → F)
    (hw₁ : isRSCodeword domain k w₁)
    (hw₂ : isRSCodeword domain k w₂)
    (hne : w₁ ≠ w₂)
    (t : ℕ) :
    (Finset.univ.filter (fun pos : Fin t → Fin N =>
      ∀ j : Fin t, w₁ (pos j) = w₂ (pos j))).card ≤ (k - 1) ^ t := by
  have hagree := rs_agreement_bound domain k hk w₁ w₂ hw₁ hw₂ hne
  set agreeSet := Finset.univ.filter (fun i : Fin N => w₁ i = w₂ i) with hagreeSet_def
  -- The bad tuples are exactly functions whose range lies in the agreement set.
  -- This is exactly Fintype.piFinset (fun _ : Fin t => agreeSet).
  have hbad_eq : Finset.univ.filter (fun pos : Fin t → Fin N =>
      ∀ j : Fin t, w₁ (pos j) = w₂ (pos j)) =
      Fintype.piFinset (fun _ : Fin t => agreeSet) := by
    ext pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      hagreeSet_def]
  rw [hbad_eq, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left hagree t

/-! ### Non-codeword detection -/

/-- A non-codeword differs from any codeword on at least one position. -/
theorem non_codeword_differs {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (word : Fin N → F) (h_not_cw : ¬isRSCodeword domain k word)
    (cw : Fin N → F) (h_cw : isRSCodeword domain k cw) :
    ∃ i : Fin N, word i ≠ cw i := by
  by_contra h
  push Not at h
  apply h_not_cw
  have heq : word = cw := funext h
  rw [heq]
  exact h_cw

/-- A non-codeword has Hamming distance at least 1 from any codeword. -/
theorem non_codeword_hamming_pos {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (word : Fin N → F) (h_not_cw : ¬isRSCodeword domain k word)
    (cw : Fin N → F) (h_cw : isRSCodeword domain k cw) :
    0 < (hammingDiffSet word cw).card := by
  rw [Finset.card_pos]
  obtain ⟨i, hi⟩ := non_codeword_differs domain k word h_not_cw cw h_cw
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- For a non-codeword, the set of positions where it agrees with any codeword
    is a proper subset of all positions. -/
theorem non_codeword_agree_proper_subset {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (word : Fin N → F) (h_not_cw : ¬isRSCodeword domain k word)
    (cw : Fin N → F) (h_cw : isRSCodeword domain k cw) :
    Finset.univ.filter (fun i => word i = cw i) ⊂ Finset.univ := by
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  obtain ⟨i, hi⟩ := non_codeword_differs domain k word h_not_cw cw h_cw
  exact ⟨i, Finset.mem_univ _, fun h => hi (Finset.mem_filter.mp h).2⟩

/-- The agreement set of a non-codeword with any codeword has strictly fewer
    than `N` elements. -/
theorem non_codeword_agree_card_lt {N : ℕ}
    (domain : EvalDomain F N) (k : ℕ)
    (word : Fin N → F) (h_not_cw : ¬isRSCodeword domain k word)
    (cw : Fin N → F) (h_cw : isRSCodeword domain k cw) :
    (Finset.univ.filter (fun i => word i = cw i)).card < N := by
  calc (Finset.univ.filter (fun i => word i = cw i)).card
      < Finset.univ.card := Finset.card_lt_card
          (non_codeword_agree_proper_subset domain k word h_not_cw cw h_cw)
    _ = N := by simp [Fintype.card_fin]
