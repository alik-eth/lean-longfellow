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
    Follows from Poseidon collision resistance. -/
theorem holderBinding_binding [PoseidonHash F 1]
    (attr1 attr2 : F)
    (h : holderBindingHash attr1 = holderBindingHash attr2) :
    attr1 = attr2 := by
  unfold holderBindingHash at h
  rw [poseidon1_eq, poseidon1_eq] at h
  exact fin1_ext (PoseidonHash.injective h)

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
    (attr1 attr2 : F) (h_diff : attr1 ≠ attr2) :
    holderBindingHash attr1 ≠ holderBindingHash attr2 := by
  intro h_eq
  exact h_diff (holderBinding_binding attr1 attr2 h_eq)
