import LeanLongfellow.Poseidon.Defs
import LeanLongfellow.Poseidon.Nullifier
import LeanLongfellow.Poseidon.HolderBinding

/-! # Concrete Poseidon Instantiation via Sponge Model

`PoseidonHash` bundles collision resistance (injectivity) as a typeclass
field. This is convenient but hides the cryptographic assumption.

`PoseidonSponge` is a more realistic model: it carries only the hash
function, and collision resistance appears as an explicit hypothesis
wherever it is needed. Given a CR hypothesis one can derive
`PoseidonHash`, so all downstream theorems (nullifier binding, holder
binding, predicate commitment binding) carry through unchanged.

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

/-- Derive `PoseidonHash` from a `PoseidonSponge` and an explicit
    collision-resistance hypothesis.

    This is the only place where the CR assumption is "consumed";
    all downstream theorems (`nullifier_binding`, `holderBinding_binding`,
    `predicateCommitment_binding`) work through the resulting
    `PoseidonHash` instance. -/
@[reducible]
def PoseidonSponge.toPoseidonHash [PoseidonSponge F n]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := n))) :
    PoseidonHash F n where
  hash := PoseidonSponge.hash
  injective := hcr

-- ============================================================
-- Section 4: Re-exported theorems via the sponge interface
-- ============================================================

/-- Nullifier binding through the sponge model.
    Same nullifier implies same credential, contract, and salt. -/
theorem nullifier_binding_from_sponge [PoseidonSponge F 3]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 3)))
    (cred1 cred2 contract1 contract2 salt1 salt2 : F)
    (heq : @nullifier F (PoseidonSponge.toPoseidonHash hcr) cred1 contract1 salt1 =
           @nullifier F (PoseidonSponge.toPoseidonHash hcr) cred2 contract2 salt2) :
    cred1 = cred2 ∧ contract1 = contract2 ∧ salt1 = salt2 :=
  @nullifier_binding F (PoseidonSponge.toPoseidonHash hcr)
    cred1 cred2 contract1 contract2 salt1 salt2 heq

/-- Holder binding through the sponge model.
    Same holder binding hash implies same first attribute. -/
theorem holderBinding_binding_from_sponge [PoseidonSponge F 1]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 1)))
    (attr1 attr2 : F)
    (heq : @holderBindingHash F (PoseidonSponge.toPoseidonHash hcr) attr1 =
           @holderBindingHash F (PoseidonSponge.toPoseidonHash hcr) attr2) :
    attr1 = attr2 :=
  @holderBinding_binding F (PoseidonSponge.toPoseidonHash hcr) attr1 attr2 heq

/-- Predicate commitment binding through the sponge model.
    Same commitment implies same inputs. -/
theorem predicateCommitment_binding_from_sponge [PoseidonSponge F 3]
    (hcr : Function.Injective (PoseidonSponge.hash (F := F) (n := 3)))
    (cv1 cv2 sd1 sd2 mh1 mh2 : F)
    (heq : @predicateCommitment F (PoseidonSponge.toPoseidonHash hcr) cv1 sd1 mh1 =
           @predicateCommitment F (PoseidonSponge.toPoseidonHash hcr) cv2 sd2 mh2) :
    cv1 = cv2 ∧ sd1 = sd2 ∧ mh1 = mh2 :=
  @predicateCommitment_binding F (PoseidonSponge.toPoseidonHash hcr)
    cv1 cv2 sd1 sd2 mh1 mh2 heq

-- ============================================================
-- Section 5: Any PoseidonHash gives a PoseidonSponge
-- ============================================================

/-- Every `PoseidonHash` instance trivially gives a `PoseidonSponge`
    (just forget the CR field). -/
instance PoseidonHash.toPoseidonSponge [PoseidonHash F n] :
    PoseidonSponge F n where
  hash := PoseidonHash.hash

/-- Round-tripping: converting a `PoseidonHash` to a `PoseidonSponge` and
    back (with the original injectivity proof) recovers the same hash. -/
theorem PoseidonSponge.roundtrip_hash [inst : PoseidonHash F n] :
    (PoseidonSponge.toPoseidonHash (F := F) (n := n)
      inst.injective).hash = PoseidonHash.hash := rfl
