import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic

/-! # Abstract Merkle Tree

A Merkle tree commits to a sequence of leaves using a collision-resistant
hash function. The commitment is the root hash. Individual leaves can be
opened with authentication paths (sibling hashes along the path to the root).

This module provides:
- `MerkleHash`: an abstract collision-resistant binary hash
- `MerkleTree`: a complete binary tree of depth `d` with `2^d` leaves
- `AuthPath`: an authentication path from leaf to root
- `verifyPath`: verification of a leaf against a root via its path
- `getLeaf` / `getPath`: extraction of leaves and their paths from a tree
-/

-- ============================================================
-- Section 1: Abstract collision-resistant binary hash
-- ============================================================

/-- Abstract hash function for Merkle tree nodes.
    Takes two children and produces a parent digest.
    Collision resistance is captured by injectivity on pairs. -/
class MerkleHash (D : Type*) where
  hash2 : D → D → D
  /-- Collision resistance: `hash2` is injective as a function of pairs. -/
  hash2_injective : Function.Injective (fun p : D × D => hash2 p.1 p.2)

-- ============================================================
-- Section 2: Merkle tree type
-- ============================================================

/-- A complete binary Merkle tree of depth `d` over digest type `D`.
    Has `2^d` leaves. -/
inductive MerkleTree (D : Type*) [MerkleHash D] : ℕ → Type _ where
  | leaf : D → MerkleTree D 0
  | node : {n : ℕ} → MerkleTree D n → MerkleTree D n → MerkleTree D (n + 1)

-- ============================================================
-- Section 3: Root hash
-- ============================================================

/-- Compute the root hash (digest) of a Merkle tree. -/
def MerkleTree.root {D : Type*} [MerkleHash D] {n : ℕ} : MerkleTree D n → D
  | .leaf d => d
  | .node l r => MerkleHash.hash2 l.root r.root

-- ============================================================
-- Section 4: Authentication paths
-- ============================================================

/-- An authentication path of depth `d`: a sequence of sibling digests
    and direction bits from leaf to root.

    Each step `(sibling, is_left)` means:
    - `is_left = true`: we are the left child, sibling is on the right
    - `is_left = false`: we are the right child, sibling is on the left -/
def AuthPath (D : Type*) (d : ℕ) := Fin d → D × Bool

/-- Verify an authentication path by reconstructing the root from a
    leaf digest. Walks from the leaf upward, hashing with each sibling
    according to the direction bit. -/
def verifyPath {D : Type*} [MerkleHash D] (leaf_digest : D) {d : ℕ}
    (path : AuthPath D d) : D :=
  match d with
  | 0 => leaf_digest
  | n + 1 =>
    let ⟨sibling, is_left⟩ := path ⟨0, Nat.zero_lt_succ n⟩
    let parent := if is_left then MerkleHash.hash2 leaf_digest sibling
                  else MerkleHash.hash2 sibling leaf_digest
    verifyPath parent (fun i => path ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩)

-- ============================================================
-- Section 5: Leaf extraction
-- ============================================================

/-- Extract the leaf digest at index `i` from a Merkle tree.
    Indices are in `Fin (2^d)`, addressed by the binary decomposition:
    left subtree gets indices `[0, 2^(d-1))`, right gets `[2^(d-1), 2^d)`. -/
def MerkleTree.getLeaf {D : Type*} [MerkleHash D] {d : ℕ}
    (tree : MerkleTree D d) (i : Fin (2^d)) : D :=
  match d, tree, i with
  | 0, .leaf v, _ => v
  | n + 1, .node l r, i =>
    if h : i.val < 2 ^ n then
      l.getLeaf ⟨i.val, h⟩
    else
      r.getLeaf ⟨i.val - 2 ^ n, by omega⟩

-- ============================================================
-- Section 6: Authentication path extraction
-- ============================================================

/-- Extract the authentication path for leaf index `i`.
    The path encodes sibling hashes and directions from the leaf to root.
    Path element 0 is the leaf's immediate sibling (bottom of the tree)
    and element `d-1` is the root-level sibling (top of the tree). -/
def MerkleTree.getPath {D : Type*} [MerkleHash D] {d : ℕ}
    (tree : MerkleTree D d) (i : Fin (2^d)) : AuthPath D d :=
  match d, tree, i with
  | 0, .leaf _, _ => fun j => Fin.elim0 j
  | n + 1, .node l r, i => fun j =>
    if h : i.val < 2 ^ n then
      -- Leaf is in left subtree
      if hj : j.val = n then
        -- Last path element: sibling is the right subtree root
        (r.root, true)
      else
        -- Earlier path elements: recurse into left subtree
        l.getPath ⟨i.val, h⟩ ⟨j.val, by omega⟩
    else
      -- Leaf is in right subtree
      if hj : j.val = n then
        -- Last path element: sibling is the left subtree root
        (l.root, false)
      else
        -- Earlier path elements: recurse into right subtree
        r.getPath ⟨i.val - 2 ^ n, by omega⟩ ⟨j.val, by omega⟩

-- ============================================================
-- Section 7: Merkle commitment
-- ============================================================

/-- A Merkle commitment is simply a root hash digest. -/
def MerkleCommitment (D : Type*) := D
