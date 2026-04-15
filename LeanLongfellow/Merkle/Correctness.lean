import LeanLongfellow.Merkle.Defs

/-! # Merkle Tree Correctness Properties

Proves the key security properties of the Merkle tree commitment scheme:

1. **Binding**: a valid authentication path uniquely determines the leaf
   value. This is the critical security property for Ligero — once the
   prover commits to a root, they cannot equivocate on any leaf.
2. **Correctness**: the authentication path extracted from a tree verifies
   against the tree's root.

Each binding theorem has two variants:
- One taking `Function.Injective` as an explicit hypothesis.
- One concluding `result ∨ MerkleHashCollision` (collision-extracting).
-/

-- ============================================================
-- Section 1: Auxiliary lemma for hash2 injectivity
-- ============================================================

/-- `hash2` is injective in its first argument (left cancellation).
    Requires injectivity of the pair hash as an explicit hypothesis. -/
theorem MerkleHash.hash2_left_cancel {D : Type*} [MerkleHash D]
    (hcr : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    {a b c : D} (h : MerkleHash.hash2 a c = MerkleHash.hash2 b c) :
    a = b := by
  have : (a, c) = (b, c) := hcr h
  exact congrArg Prod.fst this

/-- `hash2` is injective in its second argument (right cancellation).
    Requires injectivity of the pair hash as an explicit hypothesis. -/
theorem MerkleHash.hash2_right_cancel {D : Type*} [MerkleHash D]
    (hcr : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    {a b c : D} (h : MerkleHash.hash2 c a = MerkleHash.hash2 c b) :
    a = b := by
  have : (c, a) = (c, b) := hcr h
  exact congrArg Prod.snd this

-- ============================================================
-- Section 2: verifyPath step lemma
-- ============================================================

/-- `verifyPath` at depth `n+1` peels off one hash step. -/
theorem verifyPath_succ {D : Type*} [MerkleHash D] {n : ℕ}
    (v : D) (path : AuthPath D (n + 1)) :
    verifyPath v path =
      verifyPath
        (let ⟨sibling, is_left⟩ := path ⟨0, Nat.zero_lt_succ n⟩
         if is_left then MerkleHash.hash2 v sibling
         else MerkleHash.hash2 sibling v)
        (fun i : Fin n => path ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩) := by
  rfl

-- ============================================================
-- Section 3: Binding (the critical security property)
-- ============================================================

/-- **Binding**: same path, same resulting root implies same leaf.

    This is the key security property for Ligero: once the prover commits
    to a Merkle root, they cannot open any leaf position to two different
    values using the same authentication path.

    Requires collision resistance (injectivity) as an explicit hypothesis.

    Proof by induction on depth `d`:
    - Base case (`d = 0`): `verifyPath` is the identity, so the claim
      is immediate.
    - Inductive case: unfold one hash step. By the IH on the tail path,
      the intermediate parent digests are equal. Then `hash2_injective`
      (left or right cancellation) forces the original leaves to be
      equal. -/
theorem merkle_binding {D : Type*} [MerkleHash D] {d : ℕ}
    (hcr : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    (leaf1 leaf2 : D) (path : AuthPath D d)
    (h : verifyPath leaf1 path = verifyPath leaf2 path) :
    leaf1 = leaf2 := by
  induction d generalizing leaf1 leaf2 with
  | zero => exact h
  | succ n ih =>
    -- Peel off one hash step on both sides
    rw [verifyPath_succ, verifyPath_succ] at h
    -- Define the tail path for depth n
    let tail : AuthPath D n :=
      fun i => path ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩
    -- Apply IH to the recursive calls: parent digests must be equal
    have h_parent := ih _ _ tail h
    -- Case-split on the direction bit of the first path element
    by_cases hb : (path ⟨0, Nat.zero_lt_succ n⟩).2 = true
    · -- is_left = true: hash2 leaf sibling
      simp only [hb, ite_true] at h_parent
      exact MerkleHash.hash2_left_cancel hcr h_parent
    · -- is_left = false: hash2 sibling leaf
      have hb' : (path ⟨0, Nat.zero_lt_succ n⟩).2 = false := by
        exact Bool.eq_false_iff.mpr hb
      simp only [hb'] at h_parent
      exact MerkleHash.hash2_right_cancel hcr h_parent

open Classical in
/-- **Binding (collision-extracting)**: same path, same resulting root
    implies same leaf, OR a `MerkleHash` collision exists.
    Does not require the `Function.Injective` hypothesis. -/
theorem merkle_binding_or_collision {D : Type*} [MerkleHash D] {d : ℕ}
    (leaf1 leaf2 : D) (path : AuthPath D d)
    (h : verifyPath leaf1 path = verifyPath leaf2 path) :
    leaf1 = leaf2 ∨ MerkleHashCollision D := by
  by_cases hinj : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2)
  · left; exact merkle_binding hinj leaf1 leaf2 path h
  · right
    rw [injective_iff_no_collision] at hinj
    exact not_not.mp hinj

/-- **Binding (with explicit root)**: if two leaf values both verify against
    the same root using the same authentication path, then the leaves
    must be equal. Requires collision resistance as an explicit hypothesis. -/
theorem merkle_binding_root {D : Type*} [MerkleHash D] {d : ℕ}
    (hcr : Function.Injective (fun p : D × D => MerkleHash.hash2 p.1 p.2))
    (root : D) (leaf1 leaf2 : D) (path1 path2 : AuthPath D d)
    (h1 : verifyPath leaf1 path1 = root)
    (h2 : verifyPath leaf2 path2 = root)
    (h_same_path : path1 = path2) :
    leaf1 = leaf2 := by
  subst h_same_path
  exact merkle_binding hcr leaf1 leaf2 path1 (h1.trans h2.symm)

open Classical in
/-- **Binding with explicit root (collision-extracting):**
    Same conclusion as `merkle_binding_root`, OR a `MerkleHash` collision. -/
theorem merkle_binding_root_or_collision {D : Type*} [MerkleHash D] {d : ℕ}
    (root : D) (leaf1 leaf2 : D) (path1 path2 : AuthPath D d)
    (h1 : verifyPath leaf1 path1 = root)
    (h2 : verifyPath leaf2 path2 = root)
    (h_same_path : path1 = path2) :
    leaf1 = leaf2 ∨ MerkleHashCollision D := by
  subst h_same_path
  exact merkle_binding_or_collision leaf1 leaf2 path1 (h1.trans h2.symm)

-- ============================================================
-- Section 4: Correctness helper lemmas
-- ============================================================

/-- `verifyPath` at depth `n+1` can peel the LAST element instead of
    the first.  Process the first `n` elements to get an intermediate
    digest, then hash once more with the final sibling. -/
theorem verifyPath_snoc {D : Type*} [MerkleHash D] {n : ℕ}
    (v : D) (path : AuthPath D (n + 1)) :
    verifyPath v path =
      let mid := verifyPath v (fun j : Fin n => path ⟨j.val, by omega⟩)
      let ⟨sibling, is_left⟩ := path ⟨n, by omega⟩
      if is_left then MerkleHash.hash2 mid sibling
      else MerkleHash.hash2 sibling mid := by
  induction n generalizing v with
  | zero => rfl
  | succ m ih =>
    -- Unfold one step of verifyPath
    conv_lhs => rw [verifyPath_succ]
    -- Apply IH to the recursive call
    set tail : AuthPath D (m + 1) :=
      fun i => path ⟨i.val + 1, by omega⟩
    rw [ih _ tail]
    -- The last elements agree: tail ⟨m, ..⟩ = path ⟨m+1, ..⟩
    have hlast : tail ⟨m, by omega⟩ = path ⟨m + 1, by omega⟩ := by
      simp [tail]
    -- The init paths agree after one step
    have hinit : (fun j : Fin m => tail ⟨j.val, by omega⟩) =
        (fun j : Fin m => path ⟨j.val + 1, by omega⟩) := by
      rfl
    -- Rewrite tail references
    rw [hlast, hinit]
    -- Now the mid on LHS uses verifyPath parent (shifted path)
    -- and the mid on RHS uses verifyPath v (init path)
    -- They should agree after unfolding one step of the RHS's verifyPath
    congr 1

-- ============================================================
-- Section 5: Correctness (path validity)
-- ============================================================

/-- **Correctness**: the authentication path extracted from a tree
    verifies against the tree's root.

    Proof by induction on depth `d`. The key idea is that `getPath`
    produces a bottom-up path: element 0 is the leaf's immediate
    sibling, and element `d-1` is the root-level sibling. We use
    `verifyPath_snoc` to peel off the last element (root-level sibling)
    and then apply the inductive hypothesis on the subtree. -/
theorem merkle_path_valid {D : Type*} [MerkleHash D] {d : ℕ}
    (tree : MerkleTree D d) (i : Fin (2^d)) :
    verifyPath (tree.getLeaf i) (tree.getPath i) = tree.root := by
  induction d with
  | zero =>
    match tree with
    | .leaf _ => rfl
  | succ n ih =>
    match tree with
    | .node l r =>
      rw [verifyPath_snoc]
      -- Goal: let mid := ...; let ⟨s,b⟩ := path[n]; ... = hash2 l.root r.root
      by_cases h : i.val < 2 ^ n
      · -- Leaf is in left subtree
        -- Simplify getLeaf
        have hleaf : (MerkleTree.node l r).getLeaf i = l.getLeaf ⟨i.val, h⟩ := by
          simp [MerkleTree.getLeaf, h]
        -- The last path element is (r.root, true)
        have hlast : (MerkleTree.node l r).getPath i ⟨n, by omega⟩ = (r.root, true) := by
          simp [MerkleTree.getPath, h]
        -- The init path matches l.getPath
        have hinit : (fun j : Fin n =>
            (MerkleTree.node l r).getPath i ⟨j.val, by omega⟩) =
            l.getPath ⟨i.val, h⟩ := by
          funext j
          simp only [MerkleTree.getPath, h, dite_true]
          simp only [show ¬(j.val = n) from by omega, dite_false]
        rw [hleaf, hlast, hinit]
        simp only [ite_true, MerkleTree.root]
        exact congrArg (MerkleHash.hash2 · r.root) (ih l ⟨i.val, h⟩)
      · -- Leaf is in right subtree
        have hleaf : (MerkleTree.node l r).getLeaf i =
            r.getLeaf ⟨i.val - 2 ^ n, by omega⟩ := by
          simp [MerkleTree.getLeaf, h]
        have hlast : (MerkleTree.node l r).getPath i ⟨n, by omega⟩ = (l.root, false) := by
          simp [MerkleTree.getPath, h]
        have hinit : (fun j : Fin n =>
            (MerkleTree.node l r).getPath i ⟨j.val, by omega⟩) =
            r.getPath ⟨i.val - 2 ^ n, by omega⟩ := by
          funext j
          simp only [MerkleTree.getPath, h, dite_false]
          simp only [show ¬(j.val = n) from by omega, dite_false]
        rw [hleaf, hlast, hinit]
        simp only [MerkleTree.root]
        exact congrArg (MerkleHash.hash2 l.root ·) (ih r ⟨i.val - 2 ^ n, by omega⟩)
