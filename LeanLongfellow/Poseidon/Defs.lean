import Mathlib.Algebra.Field.Defs
import Mathlib.Logic.Function.Basic

/-! # Abstract Poseidon Hash Model

Poseidon is an algebraic hash function operating over field elements.
We model it as an abstract function with collision resistance (injectivity).
The internal round structure (S-boxes, MDS matrix) is not formalized —
only the security property matters for protocol correctness. -/

-- ============================================================
-- Section 1: Abstract Poseidon hash class
-- ============================================================

/-- Abstract Poseidon hash with arity `n`: takes `n` field elements, returns one.
    Collision resistance is captured by injectivity. -/
class PoseidonHash (F : Type*) (n : ℕ) where
  hash : (Fin n → F) → F
  /-- Collision resistance: distinct inputs produce distinct outputs. -/
  injective : Function.Injective hash

-- ============================================================
-- Section 2: Convenience wrappers
-- ============================================================

variable {F : Type*}

/-- Convenience: Poseidon with 3 inputs (used for commitment and nullifier). -/
noncomputable def poseidon3 [PoseidonHash F 3] (a b c : F) : F :=
  PoseidonHash.hash (fun i : Fin 3 =>
    match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c)

/-- Convenience: Poseidon with 1 input (used for holder binding). -/
noncomputable def poseidon1 [PoseidonHash F 1] (a : F) : F :=
  PoseidonHash.hash (fun _ : Fin 1 => a)

-- ============================================================
-- Section 3: Predicate commitment
-- ============================================================

/-- The commitment scheme used in zk-eIDAS predicates:
    `commitment = Poseidon(claim_value, sd_array_hash, message_hash)`. -/
noncomputable def predicateCommitment [PoseidonHash F 3]
    (claim_value sd_array_hash message_hash : F) : F :=
  poseidon3 claim_value sd_array_hash message_hash

-- ============================================================
-- Section 4: Commitment binding
-- ============================================================

/-- Auxiliary: the `Fin 3 → F` input function used by `poseidon3`. -/
private def mkInput3 {F : Type*} (a b c : F) : Fin 3 → F :=
  fun i : Fin 3 => match i with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c

/-- The `Fin 3 → F` function evaluates correctly at each index. -/
private theorem mkInput3_0 {F : Type*} (a b c : F) : mkInput3 a b c ⟨0, by omega⟩ = a := rfl
private theorem mkInput3_1 {F : Type*} (a b c : F) : mkInput3 a b c ⟨1, by omega⟩ = b := rfl
private theorem mkInput3_2 {F : Type*} (a b c : F) : mkInput3 a b c ⟨2, by omega⟩ = c := rfl

/-- `poseidon3` is defined using `mkInput3`. -/
private theorem poseidon3_eq [PoseidonHash F 3] (a b c : F) :
    poseidon3 a b c = PoseidonHash.hash (mkInput3 a b c) := rfl

/-- Extracting component equalities from function equality on `Fin 3`. -/
private theorem fin3_ext {F : Type*} {a1 a2 b1 b2 c1 c2 : F}
    (h : mkInput3 a1 b1 c1 = mkInput3 a2 b2 c2) :
    a1 = a2 ∧ b1 = b2 ∧ c1 = c2 := by
  exact ⟨congr_fun h ⟨0, by omega⟩, congr_fun h ⟨1, by omega⟩, congr_fun h ⟨2, by omega⟩⟩

/-- Commitment binding: same commitment implies same inputs.
    Follows directly from Poseidon collision resistance (injectivity). -/
theorem predicateCommitment_binding [PoseidonHash F 3]
    (cv1 cv2 sd1 sd2 mh1 mh2 : F)
    (h : predicateCommitment cv1 sd1 mh1 = predicateCommitment cv2 sd2 mh2) :
    cv1 = cv2 ∧ sd1 = sd2 ∧ mh1 = mh2 := by
  unfold predicateCommitment at h
  rw [poseidon3_eq, poseidon3_eq] at h
  exact fin3_ext (PoseidonHash.injective h)
