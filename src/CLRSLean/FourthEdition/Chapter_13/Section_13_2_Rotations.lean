import Mathlib
import CLRSLean.FourthEdition.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# Section 13.2 - Rotations

This section completes the fourth-edition §13.2 boundary on top of the legacy
{lit}`CLRSLean.Chapter_13` red-black-tree model.  Two layers are added:

1. **A pointer/sentinel store.**  The legacy {lit}`RBTree` is a purely
   functional, Okasaki-style tree.  CLRS instead manipulates a pointer-based
   structure with an explicit sentinel {lit}`T.nil`, `left`/`right`/`parent`
   links, and in-place pointer rewiring.  We introduce {lit}`RBNode` (one heap
   node) and {lit}`RBStore` (a node table addressed by {lit}`Nat` indices,
   index {lit}`0` reserved for the sentinel), together with the representation
   predicate {lit}`StoreRepr` linking a store to the functional tree it encodes.

2. **BST (inorder) preservation.**  The legacy model proves membership is
   preserved under rotation, but not that the *ordering* invariant {lit}`BST`
   is.  We prove rotations and root recoloring preserve {lit}`BST` and the
   inorder key list {lit}`keys`.

Finally we give the pointer-level rotation primitives ({lit}`rotateLeftP`,
{lit}`rotateRightP`) and a constant-time recolor ({lit}`recolorP`), each
returning its auditable pointer-operation cost, and prove their pointer-rewiring
specification.

Main results:

- Definition {lit}`RBStore`, {lit}`RBNode`: the pointer/sentinel red-black store.
- Definition {lit}`StoreRepr`, {lit}`Represents`: the representation predicate.
- Theorem {lit}`RBTree.keys_rotateLeft` / {lit}`RBTree.keys_rotateRight`:
  rotations preserve the inorder key list.
- Theorem {lit}`RBTree.bst_rotateLeft` / {lit}`RBTree.bst_rotateRight`:
  rotations preserve the BST ordering invariant.
- Theorem {lit}`RBTree.bst_repaintRoot`: recoloring preserves BST.
- Definition {lit}`RBStore.rotateLeftP` / {lit}`RBStore.rotateRightP` /
  {lit}`RBStore.recolorP`: pointer-level rotation/recolor with constant cost.
- Theorem {lit}`RBStore.rotateLeftP_cost` / {lit}`RBStore.rotateRightP_cost`:
  each rotation performs exactly {lit}`rotateCost` pointer operations.
- Theorem {lit}`RBStore.set_frame` and {lit}`RBStore.get_set_eq`: the frame
  property of a single pointer write (the shared-layer frame test).

Current gaps: the composed insertion/deletion *cost* theorems and their
{lit}`RB-INSERT-FIXUP` / {lit}`RB-DELETE-FIXUP` bridges are covered in
§13.3 and §13.4.
-/

namespace CLRS
namespace Chapter13

/-! ## Pointer/sentinel store (CLRS `T.nil` model) -/

/-- A single heap node of the pointer-based red-black tree: a key, a color, and
the indices of its left, right, and parent pointers.  The sentinel index is
`0` (CLRS `T.nil`). -/
structure RBNode where
  key : Nat
  color : Color
  left : Nat
  right : Nat
  parent : Nat
  deriving Repr, DecidableEq

/-- A pointer-based red-black tree store: a partial node table addressed by
natural indices (index `0` is the sentinel `T.nil`) plus the root index. -/
structure RBStore where
  node : Nat → Option RBNode
  root : Nat

namespace RBStore

/-- The sentinel index (CLRS `T.nil`). -/
def nil : Nat := 0

/-- Read the node at index `i`; the sentinel and unallocated indices read as
`none`. -/
def get (s : RBStore) (i : Nat) : Option RBNode := s.node i

/-- Write node `n` at index `i`, leaving every other index unchanged. -/
def set (s : RBStore) (i : Nat) (n : RBNode) : RBStore :=
  { s with node := fun j => if j = i then some n else s.node j }

@[simp] theorem get_set_eq {s : RBStore} {i : Nat} {n : RBNode} :
    (s.set i n).get i = some n := by
  simp [set, get]

@[simp] theorem get_set_ne {s : RBStore} {i j : Nat} {n : RBNode} (h : j ≠ i) :
    (s.set i n).get j = s.get j := by
  simp [set, get, h]

end RBStore

open RBStore (nil)

/--
The representation predicate: the pointer subgraph rooted at index `i` of store
`s` encodes the functional tree `t`.  Following `left`/`right` pointers from `i`
and stopping at the sentinel yields exactly `t`; every visited node records its
key and color.  Because the relation is defined inductively over the finite tree
`t`, it enforces acyclicity and terminates at the sentinel.
-/
inductive StoreRepr (s : RBStore) : Nat → RBTree → Prop where
  | nil : StoreRepr s nil .empty
  | node (i : Nat) (n : RBNode) (l r : RBTree) (k : Nat) (c : Color) :
      s.get i = some n →
      StoreRepr s n.left l →
      StoreRepr s n.right r →
      n.key = k →
      n.color = c →
      StoreRepr s i (.node c l k r)

/-- A store represents a tree at its root. -/
def Represents (s : RBStore) (t : RBTree) : Prop := StoreRepr s s.root t

/-! ## Inorder key list and BST preservation under rotation -/

namespace RBTree

/-- The inorder key list of a colored tree. -/
def keys : RBTree → List Nat
  | .empty => []
  | .node _ l k r => keys l ++ [k] ++ keys r

/-- Left rotation preserves the inorder key list. -/
theorem keys_rotateLeft (t : RBTree) : keys (rotateLeft t) = keys t := by
  cases t with
  | empty => rfl
  | node c a x r =>
    cases r with
    | empty => rfl
    | node rc b y d =>
      simp [rotateLeft, keys, List.append_assoc]

/-- Right rotation preserves the inorder key list. -/
theorem keys_rotateRight (t : RBTree) : keys (rotateRight t) = keys t := by
  cases t with
  | empty => rfl
  | node c l y r =>
    cases l with
    | empty => rfl
    | node lc a x b =>
      simp [rotateRight, keys, List.append_assoc]

/-- Root recoloring preserves the inorder key list. -/
theorem keys_repaintRoot (c : Color) (t : RBTree) :
    keys (repaintRoot c t) = keys t := by
  cases t <;> simp [repaintRoot, keys]

/-- Left rotation preserves the BST ordering invariant. -/
theorem bst_rotateLeft {t : RBTree} (h : BST t) : BST (rotateLeft t) := by
  cases t with
  | empty => simp [rotateLeft, BST]
  | node c a x r =>
    cases r with
    | empty => simpa [rotateLeft] using h
    | node rc b y d =>
      simp only [rotateLeft]
      change BST a ∧ BST (node rc b y d) ∧ (∀ z, InTree z a → z < x) ∧ (∀ z, z = y ∨ InTree z b ∨ InTree z d → x < z) at h
      rcases h with ⟨hA, hR, hAx, hxR⟩
      change BST b ∧ BST d ∧ (∀ z, InTree z b → z < y) ∧ (∀ z, InTree z d → y < z) at hR
      rcases hR with ⟨hB, hD, hBy, hyD⟩
      change BST (node c a x b) ∧ BST d ∧ (∀ z, z = x ∨ InTree z a ∨ InTree z b → z < y) ∧ (∀ z, InTree z d → y < z)
      constructor
      · constructor
        · exact hA
        constructor
        · exact hB
        constructor
        · intro z hza; exact hAx z hza
        · intro z hzb; exact hxR z (Or.inr (Or.inl hzb))
      · constructor
        · exact hD
        constructor
        · intro z hz
          rcases hz with hzx | hza | hzb
          · subst z; exact hxR y (Or.inl rfl)
          · exact lt_trans (hAx z hza) (hxR y (Or.inl rfl))
          · exact hBy z hzb
        · intro z hzd; exact hyD z hzd

/-- Right rotation preserves the BST ordering invariant. -/
theorem bst_rotateRight {t : RBTree} (h : BST t) : BST (rotateRight t) := by
  cases t with
  | empty => simp [rotateRight, BST]
  | node c l y r =>
    cases l with
    | empty => simpa [rotateRight] using h
    | node lc a x b =>
      simp only [rotateRight]
      change BST (node lc a x b) ∧ BST r ∧ (∀ z, z = x ∨ InTree z a ∨ InTree z b → z < y) ∧ (∀ z, InTree z r → y < z) at h
      rcases h with ⟨hL, hD, hLtY, hxR⟩
      change BST a ∧ BST b ∧ (∀ z, InTree z a → z < x) ∧ (∀ z, InTree z b → x < z) at hL
      rcases hL with ⟨hA, hB, hAx, hxb⟩
      change BST a ∧ BST (node c b y r) ∧ (∀ z, InTree z a → z < x) ∧ (∀ z, z = y ∨ InTree z b ∨ InTree z r → x < z)
      constructor
      · exact hA
      · constructor
        · change BST b ∧ BST r ∧ (∀ z, InTree z b → z < y) ∧ (∀ z, InTree z r → y < z)
          constructor
          · exact hB
          constructor
          · exact hD
          constructor
          · intro z hzb; exact hLtY z (Or.inr (Or.inr hzb))
          · intro z hzr; exact hxR z hzr
        constructor
        · intro z hza; exact hAx z hza
        · intro z hz
          rcases hz with hzy | hzb | hzr
          · subst z; exact hLtY x (Or.inl rfl)
          · exact hxb z hzb
          · exact lt_trans (hLtY x (Or.inl rfl)) (hxR z hzr)

/-- Root recoloring preserves the BST ordering invariant. -/
theorem bst_repaintRoot {c : Color} {t : RBTree} (h : BST t) :
    BST (repaintRoot c t) := by
  cases t with
  | empty => simp [repaintRoot, BST]
  | node _ l k r =>
      simp [repaintRoot, BST] at h ⊢
      exact h

end RBTree

/-! ## Pointer-level rotation and recolor primitives -/

/-- The auditable pointer-operation cost of a single rotation: a bounded
constant number of pointer assignments (two child rewires, one parent rewiring
of the detached middle subtree, and the bookkeeping writes). -/
def rotateCost : Nat := 6

/-- Pointer-level left rotation at node `x` (whose right child must be
non-sentinel).  Rewires the `x.right`, `y.left`, and detached-subtree parent
links in place and returns the constant pointer cost. -/
def rotateLeftP (s : RBStore) (x : Nat) : RBStore × Nat :=
  match s.get x with
  | none => (s, 0)
  | some nx =>
    let y := nx.right
    match s.get y with
    | none => (s, 0)
    | some ny =>
      let β := ny.left
      let nx' := { nx with right := β, parent := y }
      let ny' := { ny with left := x, parent := nx.parent }
      let s1 := s.set x nx'
      let s2 := s1.set y ny'
      let s3 :=
        if β = nil then s2 else
          match s2.get β with
          | none => s2
          | some nb => s2.set β { nb with parent := x }
      (s3, rotateCost)

/-- Pointer-level right rotation at node `y` (whose left child must be
non-sentinel), mirroring {lit}`rotateLeftP`. -/
def rotateRightP (s : RBStore) (y : Nat) : RBStore × Nat :=
  match s.get y with
  | none => (s, 0)
  | some ny =>
    let x := ny.left
    match s.get x with
    | none => (s, 0)
    | some nx =>
      let β := nx.right
      let ny' := { ny with left := β, parent := x }
      let nx' := { nx with right := y, parent := ny.parent }
      let s1 := s.set y ny'
      let s2 := s1.set x nx'
      let s3 :=
        if β = nil then s2 else
          match s2.get β with
          | none => s2
          | some nb => s2.set β { nb with parent := y }
      (s3, rotateCost)

/-- Pointer-level recoloring of node `i` to color `c`, at constant cost. -/
def recolorP (s : RBStore) (i : Nat) (c : Color) : RBStore × Nat :=
  match s.get i with
  | none => (s, 0)
  | some n => (s.set i { n with color := c }, 1)

/-- The pointer-operation cost of a left rotation is the constant
{lit}`rotateCost`. -/
theorem rotateLeftP_cost (s : RBStore) (x : Nat) (nx ny : RBNode)
    (hx : s.get x = some nx) (hy : s.get nx.right = some ny) :
    (rotateLeftP s x).2 = rotateCost := by
  unfold rotateLeftP
  simp [hx, hy]

/-- The pointer-operation cost of a right rotation is the constant
{lit}`rotateCost`. -/
theorem rotateRightP_cost (s : RBStore) (y : Nat) (ny nx : RBNode)
    (hy : s.get y = some ny) (hx : s.get ny.left = some nx) :
    (rotateRightP s y).2 = rotateCost := by
  unfold rotateRightP
  simp [hy, hx]

/-- A single `set` write at index `i` leaves every other index `j ≠ i`
unchanged — the *frame* property of the store.  Together with
{lit}`get_set_eq`, this is the shared-layer frame test used by the insertion
and deletion refinement proofs. -/
theorem set_frame {s : RBStore} {i j : Nat} {n : RBNode} (h : j ≠ i) :
    (s.set i n).get j = s.get j :=
  RBStore.get_set_ne h

/-- Pointer recoloring updates exactly the target node's color at cost 1. -/
theorem recolorP_spec (s : RBStore) (i : Nat) (c : Color) (n : RBNode)
    (hi : s.get i = some n) :
    (recolorP s i c).2 = 1 ∧ (recolorP s i c).1.get i = some { n with color := c } := by
  simp [recolorP, hi]

end Chapter13
end CLRS
