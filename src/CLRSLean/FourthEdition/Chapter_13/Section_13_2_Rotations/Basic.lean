import Mathlib
import CLRSLean.FourthEdition.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# Pointer rotation primitives and functional ordering

The indexed store models CLRS child and parent pointers with address zero
reserved for NIL. Rotations update the two participating records, the non-NIL
middle child's parent, and the former parent's appropriate child or the store
root. The store update is a sparse functional description of those pointer
assignments; it does not model the cost of evaluating an immutable node table.

Successful rotations return the uniform upper assignment budget six: five
required pointer assignments and the optional middle-parent assignment.
This is not an instrumented exact execution count. Representation, ownership,
frame, and actual root/interior refinement theorems are in the sibling modules.
Functional rotations preserve inorder keys and the BST ordering predicate;
they need not preserve red-black color balance without a surrounding fixup.
-/

namespace CLRS
namespace Chapter13

/-! ## Pointer/sentinel store (CLRS {lit}`T.nil` model) -/

/-- A single heap node of the pointer-based red-black tree: a key, a color, and
the indices of its left, right, and parent pointers.  The sentinel index is
{lit}`0` (CLRS {lit}`T.nil`). -/
structure RBNode where
  key : Nat
  color : Color
  left : Nat
  right : Nat
  parent : Nat
  deriving Repr, DecidableEq

/-- A pointer-based red-black tree store: a partial node table addressed by
natural indices (index {lit}`0` is the sentinel {lit}`T.nil`) plus the root index. -/
structure RBStore where
  node : Nat → Option RBNode
  root : Nat

namespace RBStore

/-- The sentinel index (CLRS {lit}`T.nil`). -/
def nil : Nat := 0

/-- Read the node table at index {lit}`i`. A valid representation requires the
sentinel to be absent; raw stores do not enforce that condition. -/
def get (s : RBStore) (i : Nat) : Option RBNode := s.node i

/-- Write node {lit}`n` at index {lit}`i`, leaving every other index unchanged. -/
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

/-- Uniform assignment budget: five pointer fields (including the old-parent
or store-root link), plus the middle child's parent when that child is non-NIL.
This budget is not an exact count of executed assignments. -/
def rotateCost : Nat := 6

/-- Replace the old subtree link in one parent record, preserving its other
child and all non-child fields. -/
def reconnectNode (oldRoot newRoot : Nat) (n : RBNode) : RBNode :=
  if n.left = oldRoot then { n with left := newRoot }
  else if n.right = oldRoot then { n with right := newRoot } else n

/-- The sparse simultaneous update performed by a rotation. On a valid tree,
the two rotated nodes, non-NIL middle root, and non-NIL former parent are
distinct, so these updates affect independent records. -/
def rotationPatch (s : RBStore) (oldRoot newRoot middle parent : Nat)
    (oldNode newNode : RBNode) : RBStore where
  root := if parent = nil then newRoot else s.root
  node j :=
    if j = oldRoot then some oldNode
    else if j = newRoot then some newNode
    else if j = middle ∧ middle ≠ nil then
      (s.get j).map (fun n => { n with parent := oldRoot })
    else if j = parent ∧ parent ≠ nil then
      (s.get j).map (reconnectNode oldRoot newRoot)
    else s.get j

/-- Left rotation rewires both participating nodes, the non-NIL middle child's
parent, and either the old parent's child link or the store root. -/
def rotateLeftP (s : RBStore) (x : Nat) : RBStore × Nat :=
  match s.get x with
  | none => (s, 0)
  | some nx =>
      match s.get nx.right with
      | none => (s, 0)
      | some ny =>
          (rotationPatch s x nx.right ny.left nx.parent
            { nx with right := ny.left, parent := nx.right }
            { ny with left := x, parent := nx.parent }, rotateCost)

/-- Right rotation is the symmetric sparse pointer update. -/
def rotateRightP (s : RBStore) (y : Nat) : RBStore × Nat :=
  match s.get y with
  | none => (s, 0)
  | some ny =>
      match s.get ny.left with
      | none => (s, 0)
      | some nx =>
          (rotationPatch s y ny.left nx.right ny.parent
            { ny with left := nx.right, parent := ny.left }
            { nx with right := y, parent := ny.parent }, rotateCost)

/-- Pointer-level recoloring of node {lit}`i` to color {lit}`c`, at constant cost. -/
def recolorP (s : RBStore) (i : Nat) (c : Color) : RBStore × Nat :=
  match s.get i with
  | none => (s, 0)
  | some n => (s.set i { n with color := c }, 1)

/-- The assignment budget returned by a left rotation is the constant
{lit}`rotateCost`. -/
theorem rotateLeftP_cost (s : RBStore) (x : Nat) (nx ny : RBNode)
    (hx : s.get x = some nx) (hy : s.get nx.right = some ny) :
    (rotateLeftP s x).2 = rotateCost := by
  unfold rotateLeftP
  simp [hx, hy]

/-- The assignment budget returned by a right rotation is the constant
{lit}`rotateCost`. -/
theorem rotateRightP_cost (s : RBStore) (y : Nat) (ny nx : RBNode)
    (hy : s.get y = some ny) (hx : s.get ny.left = some nx) :
    (rotateRightP s y).2 = rotateCost := by
  unfold rotateRightP
  simp [hy, hx]

/-- A single {lit}`set` write at index {lit}`i` leaves every other index {lit}`j ≠ i`
unchanged: the frame property of a single indexed-store write. -/
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
