import LeanLongfellow.Poseidon.Defs
import LeanLongfellow.Poseidon.Nullifier
import LeanLongfellow.Poseidon.HolderBinding

/-! # Concrete Poseidon Instantiation via Sponge Model

`PoseidonSponge` is a sponge-based hash model. Given a `PoseidonSponge`,
one can derive a `PoseidonHash` instance (both now carry only the hash
function, with collision resistance as an explicit hypothesis).
All downstream theorems (nullifier binding, holder binding, predicate
commitment binding) take CR as an explicit parameter.

## Main definitions

- `PoseidonParams` -- permutation parameters (state width, round counts)
- `PoseidonSponge` -- abstract sponge construction (hash only, no CR field)
- `PoseidonSponge.toPoseidonHash` -- bridge: sponge + CR hypothesis => `PoseidonHash`

## Main theorems (re-exports through the sponge interface)

- `nullifier_binding_from_sponge`
- `holderBinding_binding_from_sponge`
- `predicateCommitment_binding_from_sponge`
-/

-- ============================================================
-- Section 1: Poseidon permutation parameters
-- ============================================================

/-- Poseidon permutation parameters.
    These characterise the concrete instantiation but are not used in
    our abstract proofs -- they exist for documentation and future
    refinement. -/
structure PoseidonParams where
  /-- State width (typically 3 for t = 3) -/
  t : ℕ
  /-- Number of full rounds -/
  RF : ℕ
  /-- Number of partial rounds -/
  RP : ℕ

-- ============================================================
-- Section 2: PoseidonSponge class
-- ============================================================

/-- Abstract Poseidon sponge construction.

    Unlike `PoseidonHash`, this class carries **only** the hash function.
    Collision resistance is not a field; instead it appears as an explicit
    hypothesis in every theorem that needs it. This makes the CR
    assumption visible and auditable. -/
class PoseidonSponge (F : Type*) (n : ℕ) where
  /-- The hash function mapping `n` field elements to one. -/
  hash : (Fin n → F) → F

-- ============================================================
-- Section 3: Bridge to PoseidonHash
-- ============================================================

variable {F : Type*} {n : ℕ}

/-- Derive `PoseidonHash` from a `PoseidonSponge`. -/
@[reducible]
def PoseidonSponge.toPoseidonHash [PoseidonSponge F n] :
    PoseidonHash F n where
  hash := PoseidonSponge.hash

-- ============================================================
-- Section 4: Re-exported theorems via the sponge interface
-- ============================================================

/-- Nullifier binding through the sponge model.
    Same nullifier implies same credential, contract, and salt. -/
theorem nullifier_binding_from_sponge [PoseidonSponge F 3]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 3)))
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (heq : @nullifier F PoseidonSponge.toPoseidonHash cred1 contract1 salt1 =
           @nullifier F PoseidonSponge.toPoseidonHash cred2 contract2 salt2) :
    cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2 :=
  @nullifier_binding F PoseidonSponge.toPoseidonHash
    cred1 cred2 contract1 contract2 salt1 salt2 hcr heq

/-- Holder binding through the sponge model.
    Same holder binding hash implies same first attribute. -/
theorem holderBinding_binding_from_sponge [PoseidonSponge F 1]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 1)))
    (attr1 attr2 : F)
    (heq : @holderBindingHash F PoseidonSponge.toPoseidonHash attr1 =
           @holderBindingHash F PoseidonSponge.toPoseidonHash attr2) :
    attr1 = attr2 :=
  @holderBinding_binding F PoseidonSponge.toPoseidonHash attr1 attr2 hcr heq

/-- Predicate commitment binding through the sponge model.
    Same commitment implies same inputs. -/
theorem predicateCommitment_binding_from_sponge [PoseidonSponge F 3]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 3)))
    (cv1 cv2 sd1 sd2 mh1 mh2 : F)
    (heq : @predicateCommitment F PoseidonSponge.toPoseidonHash cv1 sd1 mh1 =
           @predicateCommitment F PoseidonSponge.toPoseidonHash cv2 sd2 mh2) :
    cv1 = cv2 ∧ sd1 = sd2 ∧ mh1 = mh2 :=
  @predicateCommitment_binding F PoseidonSponge.toPoseidonHash
    cv1 cv2 sd1 sd2 mh1 mh2 hcr heq

-- ============================================================
-- Section 5: Any PoseidonHash gives a PoseidonSponge
-- ============================================================

/-- Every `PoseidonHash` instance trivially gives a `PoseidonSponge`. -/
instance PoseidonHash.toPoseidonSponge [PoseidonHash F n] :
    PoseidonSponge F n where
  hash := PoseidonHash.hash

/-- Round-tripping: converting a `PoseidonHash` to a `PoseidonSponge` and
    back recovers the same hash. -/
theorem PoseidonSponge.roundtrip_hash [inst : PoseidonHash F n] :
    (PoseidonSponge.toPoseidonHash (F := F) (n := n)).hash = PoseidonHash.hash := rfl
