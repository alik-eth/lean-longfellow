import LeanLongfellow.Poseidon.Defs

/-! # Holder Binding Correctness

Holder binding hash: `Poseidon(first_attribute)`.
Enables cross-credential linking — proofs from the same holder produce
the same binding hash, while different holders produce different hashes. -/

variable {F : Type*}

-- ============================================================
-- Section 1: Holder binding computation
-- ============================================================

/-- Compute holder binding hash: `Poseidon(first_attribute)`. -/
noncomputable def holderBindingHash [PoseidonHash F 1] (first_attr : F) : F :=
  poseidon1 first_attr

-- ============================================================
-- Section 2: Binding
-- ============================================================

/-- Auxiliary: the `Fin 1 → F` input function used by `poseidon1`. -/
private def mkInput1 {F : Type*} (a : F) : Fin 1 → F :=
  fun _ : Fin 1 => a

/-- `poseidon1` is defined using `mkInput1`. -/
private theorem poseidon1_eq [PoseidonHash F 1] (a : F) :
    poseidon1 a = PoseidonHash.hash (mkInput1 a) := rfl

/-- Extracting the value from function equality on `Fin 1`. -/
private theorem fin1_ext {F : Type*} {a1 a2 : F}
    (h : mkInput1 a1 = mkInput1 a2) :
    a1 = a2 := by
  exact congr_fun h ⟨0, by omega⟩

/-- Binding: same hash implies same attribute.
    Requires Poseidon collision resistance as an explicit hypothesis. -/
theorem holderBinding_binding [PoseidonHash F 1]
    (attr1 attr2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 1)))
    (h : holderBindingHash attr1 = holderBindingHash attr2) :
    attr1 = attr2 := by
  unfold holderBindingHash at h
  rw [poseidon1_eq, poseidon1_eq] at h
  exact fin1_ext (hcr h)

-- ============================================================
-- Section 3: Consistency
-- ============================================================

/-- Same holder (same first attribute) produces same binding hash. -/
theorem holderBinding_consistent [PoseidonHash F 1]
    (attr : F) :
    holderBindingHash attr = holderBindingHash attr := rfl

-- ============================================================
-- Section 4: Distinguishing
-- ============================================================

/-- Different holders produce different binding hashes.
    Contrapositive of binding. -/
theorem holderBinding_distinguishing [PoseidonHash F 1]
    (attr1 attr2 : F)
    (hcr : Function.Injective (PoseidonHash.hash (F := F) (n := 1)))
    (h_diff : attr1 ≠ attr2) :
    holderBindingHash attr1 ≠ holderBindingHash attr2 := by
  intro h_eq
  exact h_diff (holderBinding_binding attr1 attr2 hcr h_eq)

-- ============================================================
-- Section 5: Collision-extracting reductions
-- ============================================================

open Classical in
/-- **Holder binding (collision-extracting):**
    Same binding hash implies same attribute, OR a Poseidon collision exists.
    Unlike `holderBinding_binding`, this does not require the
    `Function.Injective` hypothesis, making it non-vacuous for finite fields. -/
theorem holderBinding_binding_or_collision [PoseidonHash F 1]
    (attr1 attr2 : F)
    (h : holderBindingHash attr1 = holderBindingHash attr2) :
    attr1 = attr2 ∨ PoseidonCollision F 1 := by
  unfold holderBindingHash at h
  rw [poseidon1_eq, poseidon1_eq] at h
  by_cases heq : mkInput1 attr1 = mkInput1 attr2
  · left; exact fin1_ext heq
  · right; exact ⟨_, _, heq, h⟩

open Classical in
/-- **Holder binding distinguishing (collision-extracting):**
    Different attributes with the same binding hash imply a Poseidon collision.
    Contrapositive formulation that delegates to `holderBinding_binding_or_collision`. -/
theorem holderBinding_distinguishing_or_collision [PoseidonHash F 1]
    (attr1 attr2 : F)
    (h_diff : attr1 ≠ attr2)
    (h : holderBindingHash attr1 = holderBindingHash attr2) :
    PoseidonCollision F 1 := by
  rcases holderBinding_binding_or_collision attr1 attr2 h with heq | hcol
  · exact absurd heq h_diff
  · exact hcol
