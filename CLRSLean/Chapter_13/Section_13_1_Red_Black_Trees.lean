import Mathlib

/-!
# CLRS Section 13.1 - Red-black trees

This section develops the red-black-tree model and proves the local invariants
needed for insertion.  It starts with rotations, root recoloring, and the bundled
local red-black shape predicate, then adds the executable Okasaki-style
single-step balancer and the full recursive {lit}`RB-INSERT-FIXUP`.  Finally it
proves that the executable {lit}`RBTree.insert` preserves membership, preserves
red-black shape, and can increase black height by at most one.

Main results:

- Theorem {lit}`RBTree.inTree_rotateLeft_iff`: left rotation preserves tree
  membership.
- Theorem {lit}`RBTree.inTree_rotateRight_iff`: right rotation preserves tree
  membership.
- Theorem {lit}`RBTree.noRedRed_repaint_black`: repainting the root black
  preserves the no-red-red invariant.
- Theorem {lit}`RBTree.inTree_repaintRoot_iff`: repainting the root preserves
  membership.
- Theorem {lit}`RBTree.balancedBlackHeight_repaintRoot`: repainting the root
  preserves balanced child black heights.
- Theorem {lit}`RBTree.balancedBlackHeight_rotateLeft_red_red`: left rotation
  across a red-red edge preserves child black-height balance.
- Theorem {lit}`RBTree.balancedBlackHeight_rotateRight_red_red`: right rotation
  across a red-red edge preserves child black-height balance.
- Theorem {lit}`RBTree.redBlackShape_repaint_rotateLeft_red_red`: the left
  red-red rotation case followed by repainting the new root black establishes
  the bundled local red-black shape invariant.
- Theorem {lit}`RBTree.redBlackShape_repaint_rotateRight_red_red`: the
  symmetric right red-red rotation case followed by repainting the new root
  black establishes the bundled local red-black shape invariant.
- Theorem {lit}`RBTree.redBlackShape_repaint_black`: repainting the root black
  establishes the bundled local red-black shape invariant.
- Definitions {lit}`RBTree.balanceLeft`, {lit}`RBTree.balanceRight`,
  {lit}`RBTree.insertFixup`, and {lit}`RBTree.insert`: executable insertion.
- Theorem {lit}`RBTree.inTree_insert_iff`: insertion preserves membership.
- Theorem {lit}`RBTree.redBlackShape_insert`: insertion preserves red-black
  shape.
- Theorem {lit}`RBTree.blackHeight_insertFixup`: {lit}`insertFixup` preserves
  the original black height.
- Theorem {lit}`RBTree.blackHeight_insert`: insertion either keeps the black
  height or increases it by one.
- Theorem {lit}`RBTree.height_log_bound`: **CLRS Lemma 13.1** — a red-black
  tree with {lit}`n` internal nodes has height at most {lit}`2 log₂(n + 1)`.
- Definitions {lit}`RBTree.deleteFixupCase1`..{lit}`deleteFixupCase4` and the
  {lit}`deleteFixupLocal` dispatcher: the four local {lit}`RB-DELETE-FIXUP`
  cases (deficient left child).
- Theorems {lit}`RBTree.inTree_deleteFixupCase1_iff`..{lit}`_case4_iff`: every
  delete-fixup case preserves membership.
- Theorem {lit}`RBTree.deleteFixupCase4_shape`: the terminating rotation case
  resolves the doubly-black deficit and re-establishes the no-red-red and
  balanced-black-height invariants.
- Definitions {lit}`RBTree.BST`, {lit}`RBTree.splitMin`, {lit}`RBTree.join`,
  {lit}`RBTree.del`, and {lit}`RBTree.delete`: executable functional deletion
  for red-black trees (Okasaki/Kahrs pattern).
- Theorem {lit}`RBTree.inTree_splitMin_mem`: the minimum removed by
  {lit}`splitMin` is in the original tree.
- Theorem {lit}`RBTree.inTree_splitMin_iff`: membership preservation through
  {lit}`splitMin`.
- Theorem {lit}`RBTree.inTree_join_iff`: {lit}`join` preserves the union of key
  sets.
- Theorem {lit}`RBTree.inTree_del_forward` and
  {lit}`RBTree.inTree_del_backward`: {lit}`del` preserves membership for all
  keys except the deleted key.
- Theorem {lit}`RBTree.inTree_delete_forward` and
  {lit}`RBTree.inTree_delete_backward`: same for {lit}`delete`.
- Theorem {lit}`RBTree.not_inTree_del_self` (requires BST): the deleted key is
  absent from the result.
- Theorem {lit}`RBTree.not_inTree_delete_self` (requires BST): same for
  {lit}`delete`.
- Theorem {lit}`RBTree.inTree_del_iff` and {lit}`RBTree.inTree_delete_iff`
  (requires BST): full membership-after-deletion equivalence.
- Theorem {lit}`RBTree.baldL_shape` (and its mirror {lit}`baldR_shape`):
  the rebalancers absorb a one-level black-height deficit, restoring
  {lit}`NoRedRed2` and balanced black height.
- Theorem {lit}`RBTree.splitMin_invariant`: {lit}`splitMin` (which rebalances
  on the way back up, like {lit}`del`) preserves {lit}`NoRedRed2` and balanced
  black height, with black height dropping by one only at a black root.
- Theorem {lit}`RBTree.del_invariant`: the inductive deletion certificate —
  {lit}`del` preserves {lit}`NoRedRed2` and balanced black height, with the
  black height unchanged at a red root and unchanged or one less at a black
  root.
- Theorem {lit}`RBTree.redBlackShape_delete`: **deletion preserves red-black
  shape**, proved by repainting the root black.  ({lit}`splitMin` and
  {lit}`join` rebalance the doubly-black deficit; {lit}`join` rebuilds a red
  node directly when the right subtree is red-rooted.)
-/

namespace CLRS
namespace Chapter13

/-! **Colored tree model** -/

/-- The two colors used by a red-black tree node. -/
inductive Color where
  | red
  | black
  deriving Repr, DecidableEq

/-- A colored binary tree of natural-number keys. -/
inductive RBTree where
  | empty : RBTree
  | node : Color → RBTree → Nat → RBTree → RBTree
  deriving Repr, DecidableEq

namespace RBTree

/-- Membership of a key in a colored binary tree. -/
def InTree (x : Nat) : RBTree → Prop
  | empty => False
  | node _ left key right => x = key ∨ InTree x left ∨ InTree x right

/-- The root is black; empty trees count as black leaves. -/
def RootBlack : RBTree → Prop
  | empty => True
  | node color _ _ _ => color = Color.black

/-- No red node has a red child. -/
def NoRedRed : RBTree → Prop
  | empty => True
  | node color left _ right =>
      NoRedRed left ∧ NoRedRed right ∧
        (color = Color.red → RootBlack left ∧ RootBlack right)

/--
The black height measured along the left spine.  This is meaningful together
with {lit}`BalancedBlackHeight`, which states that both child subtrees have the
same black height at every node.
-/
def blackHeight : RBTree → Nat
  | empty => 0
  | node color left _ _ =>
      blackHeight left + if color = Color.black then 1 else 0

/-- Every node has left and right subtrees with equal black height. -/
def BalancedBlackHeight : RBTree → Prop
  | empty => True
  | node _ left _ right =>
      BalancedBlackHeight left ∧ BalancedBlackHeight right ∧
        blackHeight left = blackHeight right

/--
The local red-black shape invariant used by this first model: the root is black,
there is no red-red edge, and child black heights are balanced at every node.
-/
def RedBlackShape (t : RBTree) : Prop :=
  RootBlack t ∧ NoRedRed t ∧ BalancedBlackHeight t

/-! **Rotations preserve membership** -/

/-- The local left rotation used by red-black tree balancing. -/
def rotateLeft : RBTree → RBTree
  | node color a x (node rightColor b y c) =>
      node rightColor (node color a x b) y c
  | t => t

/-- The local right rotation used by red-black tree balancing. -/
def rotateRight : RBTree → RBTree
  | node color (node leftColor a x b) y c =>
      node leftColor a x (node color b y c)
  | t => t

/-- Left rotation preserves membership of keys. -/
theorem inTree_rotateLeft_iff (x : Nat) (t : RBTree) :
    InTree x (rotateLeft t) ↔ InTree x t := by
  cases t with
  | empty =>
      simp [rotateLeft, InTree]
  | node color left key right =>
      cases right with
      | empty =>
          simp [rotateLeft]
      | node rightColor b y c =>
          simp [rotateLeft, InTree, or_assoc, or_left_comm]

/-- Right rotation preserves membership of keys. -/
theorem inTree_rotateRight_iff (x : Nat) (t : RBTree) :
    InTree x (rotateRight t) ↔ InTree x t := by
  cases t with
  | empty =>
      simp [rotateRight, InTree]
  | node color left key right =>
      cases left with
      | empty =>
          simp [rotateRight]
      | node leftColor a y b =>
          simp [rotateRight, InTree, or_left_comm, or_comm]

/-! **Local red-black invariants** -/

/-- Repaint the root of a nonempty tree, leaving empty trees unchanged. -/
def repaintRoot (color : Color) : RBTree → RBTree
  | empty => empty
  | node _ left key right => node color left key right

/-- Repainting the root preserves membership of keys. -/
theorem inTree_repaintRoot_iff (color : Color) (x : Nat) (t : RBTree) :
    InTree x (repaintRoot color t) ↔ InTree x t := by
  cases t <;> simp [repaintRoot, InTree]

/-- A red node satisfying {lit}`NoRedRed` has black children. -/
theorem red_node_children_black {left right : RBTree} {key : Nat}
    (h : NoRedRed (node Color.red left key right)) :
    RootBlack left ∧ RootBlack right := by
  exact h.2.2 rfl

/-- Repainting the root black preserves the no-red-red invariant. -/
theorem noRedRed_repaint_black {t : RBTree}
    (h : NoRedRed t) : NoRedRed (repaintRoot Color.black t) := by
  cases t with
  | empty =>
      trivial
  | node color left key right =>
      simp [repaintRoot, NoRedRed]
      exact ⟨h.1, h.2.1⟩

/-- Repainting the root preserves balanced child black heights. -/
theorem balancedBlackHeight_repaintRoot (color : Color) {t : RBTree}
    (h : BalancedBlackHeight t) :
    BalancedBlackHeight (repaintRoot color t) := by
  cases t with
  | empty =>
      trivial
  | node oldColor left key right =>
      simpa [repaintRoot, BalancedBlackHeight] using h

/-- A left rotation across a red-red edge preserves child black-height balance. -/
theorem balancedBlackHeight_rotateLeft_red_red
    {a b c : RBTree} {x y : Nat}
    (h : BalancedBlackHeight
      (node Color.red a x (node Color.red b y c))) :
    BalancedBlackHeight
      (rotateLeft (node Color.red a x (node Color.red b y c))) := by
  rcases h with ⟨ha, ⟨hb, hc, hbc⟩, hab⟩
  simp [rotateLeft, BalancedBlackHeight] at hab hbc ⊢
  exact ⟨⟨ha, hb, hab⟩, hc, hab.trans hbc⟩

/-- A right rotation across a red-red edge preserves child black-height balance. -/
theorem balancedBlackHeight_rotateRight_red_red
    {a b c : RBTree} {x y : Nat}
    (h : BalancedBlackHeight
      (node Color.red (node Color.red a x b) y c)) :
    BalancedBlackHeight
      (rotateRight (node Color.red (node Color.red a x b) y c)) := by
  rcases h with ⟨⟨ha, hb, hab⟩, hc, hac⟩
  simp [rotateRight, BalancedBlackHeight] at hab hac ⊢
  exact ⟨ha, ⟨hb, hc, hab.symm.trans hac⟩, hab⟩

/-- Repainting the root black makes the root black. -/
theorem rootBlack_repaint_black (t : RBTree) :
    RootBlack (repaintRoot Color.black t) := by
  cases t <;> simp [repaintRoot, RootBlack]

/--
Repainting the root black establishes the bundled local red-black shape
invariant, provided the no-red-red and black-height invariants already hold.
-/
theorem redBlackShape_repaint_black {t : RBTree}
    (hNoRed : NoRedRed t) (hBalanced : BalancedBlackHeight t) :
    RedBlackShape (repaintRoot Color.black t) := by
  exact ⟨
    rootBlack_repaint_black t,
    noRedRed_repaint_black hNoRed,
    balancedBlackHeight_repaintRoot Color.black hBalanced
  ⟩

/--
The local left-rotation red-red repair case: when the three fringe subtrees are
already red-black shaped and have matching black heights, rotating across the
red-red edge and repainting the new root black establishes the bundled shape
invariant.
-/
theorem redBlackShape_repaint_rotateLeft_red_red
    {a b c : RBTree} {x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b) (hc : RedBlackShape c)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c) :
    RedBlackShape
      (repaintRoot Color.black
        (rotateLeft (node Color.red a x (node Color.red b y c)))) := by
  rcases ha with ⟨haRoot, haNoRed, haBalanced⟩
  rcases hb with ⟨hbRoot, hbNoRed, hbBalanced⟩
  rcases hc with ⟨_, hcNoRed, hcBalanced⟩
  simp [RedBlackShape, repaintRoot, rotateLeft, RootBlack, NoRedRed,
    BalancedBlackHeight]
  exact ⟨
    ⟨⟨haNoRed, hbNoRed, haRoot, hbRoot⟩, hcNoRed⟩,
    ⟨⟨haBalanced, hbBalanced, hab⟩, hcBalanced, hab.trans hbc⟩
  ⟩

/--
The symmetric right-rotation red-red repair case: when the three fringe subtrees
are already red-black shaped and have matching black heights, rotating across
the red-red edge and repainting the new root black establishes the bundled
shape invariant.
-/
theorem redBlackShape_repaint_rotateRight_red_red
    {a b c : RBTree} {x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b) (hc : RedBlackShape c)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c) :
    RedBlackShape
      (repaintRoot Color.black
        (rotateRight (node Color.red (node Color.red a x b) y c))) := by
  rcases ha with ⟨_, haNoRed, haBalanced⟩
  rcases hb with ⟨hbRoot, hbNoRed, hbBalanced⟩
  rcases hc with ⟨hcRoot, hcNoRed, hcBalanced⟩
  simp [RedBlackShape, repaintRoot, rotateRight, RootBlack, NoRedRed,
    BalancedBlackHeight]
  exact ⟨
    ⟨haNoRed, hbNoRed, hcNoRed, hbRoot, hcRoot⟩,
    ⟨haBalanced, ⟨hbBalanced, hcBalanced, hbc⟩, hab⟩
  ⟩

/-! **Local insertion-fixup cases** -/

/-- The left-left red-red insertion-fixup shape. -/
def insertFixupLeftLeft : RBTree → RBTree
  | node Color.black (node Color.red (node Color.red a w b) x c) y d =>
      node Color.black (node Color.red a w b) x (node Color.red c y d)
  | t => t

/-- The left-right red-red insertion-fixup shape. -/
def insertFixupLeftRight : RBTree → RBTree
  | node Color.black (node Color.red a w (node Color.red b x c)) y d =>
      node Color.black (node Color.red a w b) x (node Color.red c y d)
  | t => t

/-- The right-left red-red insertion-fixup shape. -/
def insertFixupRightLeft : RBTree → RBTree
  | node Color.black a w (node Color.red (node Color.red b x c) y d) =>
      node Color.black (node Color.red a w b) x (node Color.red c y d)
  | t => t

/-- The right-right red-red insertion-fixup shape. -/
def insertFixupRightRight : RBTree → RBTree
  | node Color.black a w (node Color.red b x (node Color.red c y d)) =>
      node Color.black (node Color.red a w b) x (node Color.red c y d)
  | t => t

/-- The four local CLRS insertion-fixup branch orientations. -/
inductive InsertFixupCase where
  | leftLeft
  | leftRight
  | rightLeft
  | rightRight
  deriving Repr, DecidableEq

/--
Unified dispatcher for the four local insertion-fixup rewrites.  The explicit
case parameter records the branch chosen by the surrounding insertion-fixup
algorithm; the raw local tree shape alone is not enough to disambiguate every
overlapping pattern.
-/
def insertFixupLocal : InsertFixupCase → RBTree → RBTree
  | InsertFixupCase.leftLeft, t => insertFixupLeftLeft t
  | InsertFixupCase.leftRight, t => insertFixupLeftRight t
  | InsertFixupCase.rightLeft, t => insertFixupRightLeft t
  | InsertFixupCase.rightRight, t => insertFixupRightRight t

/--
The reusable local certificate needed by a future executable insertion-fixup:
the local rewrite preserves membership for a query, preserves subtree black
height, and establishes the bundled local red-black shape invariant.
-/
structure InsertFixupLocalCertificate
    (q : Nat) (before after : RBTree) : Prop where
  membership : InTree q after ↔ InTree q before
  blackHeight_eq : blackHeight after = blackHeight before
  shape : RedBlackShape after

/--
A black root with two red children is locally red-black shaped when the four
fringe subtrees are red-black shaped and have matching black heights.
-/
theorem redBlackShape_black_with_red_children
    {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    RedBlackShape
      (node Color.black (node Color.red a w b) x (node Color.red c y d)) := by
  rcases ha with ⟨haRoot, haNoRed, haBalanced⟩
  rcases hb with ⟨hbRoot, hbNoRed, hbBalanced⟩
  rcases hc with ⟨hcRoot, hcNoRed, hcBalanced⟩
  rcases hd with ⟨hdRoot, hdNoRed, hdBalanced⟩
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]
  exact ⟨
    ⟨⟨haNoRed, hbNoRed, haRoot, hbRoot⟩,
      ⟨hcNoRed, hdNoRed, hcRoot, hdRoot⟩⟩,
    ⟨⟨haBalanced, hbBalanced, hab⟩,
      ⟨hcBalanced, hdBalanced, hcd⟩,
      hab.trans hbc⟩
  ⟩

/-- The left-left insertion-fixup case preserves membership on its local shape. -/
theorem inTree_insertFixup_leftLeft_iff
    (q : Nat) (a b c d : RBTree) (w x y : Nat) :
    InTree q
        (insertFixupLeftLeft
          (node Color.black (node Color.red (node Color.red a w b) x c) y d)) ↔
      InTree q
        (node Color.black (node Color.red (node Color.red a w b) x c) y d) := by
  simp [insertFixupLeftLeft, InTree, or_assoc, or_left_comm]

/-- The left-right insertion-fixup case preserves membership on its local shape. -/
theorem inTree_insertFixup_leftRight_iff
    (q : Nat) (a b c d : RBTree) (w x y : Nat) :
    InTree q
        (insertFixupLeftRight
          (node Color.black (node Color.red a w (node Color.red b x c)) y d)) ↔
      InTree q
        (node Color.black (node Color.red a w (node Color.red b x c)) y d) := by
  simp [insertFixupLeftRight, InTree, or_assoc, or_left_comm]

/-- The right-left insertion-fixup case preserves membership on its local shape. -/
theorem inTree_insertFixup_rightLeft_iff
    (q : Nat) (a b c d : RBTree) (w x y : Nat) :
    InTree q
        (insertFixupRightLeft
          (node Color.black a w (node Color.red (node Color.red b x c) y d))) ↔
      InTree q
        (node Color.black a w (node Color.red (node Color.red b x c) y d)) := by
  simp [insertFixupRightLeft, InTree, or_assoc, or_left_comm]

/-- The right-right insertion-fixup case preserves membership on its local shape. -/
theorem inTree_insertFixup_rightRight_iff
    (q : Nat) (a b c d : RBTree) (w x y : Nat) :
    InTree q
        (insertFixupRightRight
          (node Color.black a w (node Color.red b x (node Color.red c y d)))) ↔
      InTree q
        (node Color.black a w (node Color.red b x (node Color.red c y d))) := by
  simp [insertFixupRightRight, InTree, or_assoc, or_left_comm]

/-- The left-left insertion-fixup case preserves local black height. -/
theorem blackHeight_insertFixup_leftLeft
    (a b c d : RBTree) (w x y : Nat) :
    blackHeight
        (insertFixupLeftLeft
          (node Color.black (node Color.red (node Color.red a w b) x c) y d)) =
      blackHeight
        (node Color.black (node Color.red (node Color.red a w b) x c) y d) := by
  simp [insertFixupLeftLeft, blackHeight]

/-- The left-right insertion-fixup case preserves local black height. -/
theorem blackHeight_insertFixup_leftRight
    (a b c d : RBTree) (w x y : Nat) :
    blackHeight
        (insertFixupLeftRight
          (node Color.black (node Color.red a w (node Color.red b x c)) y d)) =
      blackHeight
        (node Color.black (node Color.red a w (node Color.red b x c)) y d) := by
  simp [insertFixupLeftRight, blackHeight]

/-- The right-left insertion-fixup case preserves local black height. -/
theorem blackHeight_insertFixup_rightLeft
    (a b c d : RBTree) (w x y : Nat) :
    blackHeight
        (insertFixupRightLeft
          (node Color.black a w (node Color.red (node Color.red b x c) y d))) =
      blackHeight
        (node Color.black a w (node Color.red (node Color.red b x c) y d)) := by
  simp [insertFixupRightLeft, blackHeight]

/-- The right-right insertion-fixup case preserves local black height. -/
theorem blackHeight_insertFixup_rightRight
    (a b c d : RBTree) (w x y : Nat) :
    blackHeight
        (insertFixupRightRight
          (node Color.black a w (node Color.red b x (node Color.red c y d)))) =
      blackHeight
        (node Color.black a w (node Color.red b x (node Color.red c y d))) := by
  simp [insertFixupRightRight, blackHeight]

/-- The left-left local insertion-fixup case establishes red-black shape. -/
theorem redBlackShape_insertFixup_leftLeft
    {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    RedBlackShape
      (insertFixupLeftLeft
        (node Color.black (node Color.red (node Color.red a w b) x c) y d)) := by
  simpa [insertFixupLeftLeft] using
    redBlackShape_black_with_red_children
      (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
      ha hb hc hd hab hbc hcd

/-- The left-right local insertion-fixup case establishes red-black shape. -/
theorem redBlackShape_insertFixup_leftRight
    {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    RedBlackShape
      (insertFixupLeftRight
        (node Color.black (node Color.red a w (node Color.red b x c)) y d)) := by
  simpa [insertFixupLeftRight] using
    redBlackShape_black_with_red_children
      (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
      ha hb hc hd hab hbc hcd

/-- The right-left local insertion-fixup case establishes red-black shape. -/
theorem redBlackShape_insertFixup_rightLeft
    {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    RedBlackShape
      (insertFixupRightLeft
        (node Color.black a w (node Color.red (node Color.red b x c) y d))) := by
  simpa [insertFixupRightLeft] using
    redBlackShape_black_with_red_children
      (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
      ha hb hc hd hab hbc hcd

/-- The right-right local insertion-fixup case establishes red-black shape. -/
theorem redBlackShape_insertFixup_rightRight
    {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    RedBlackShape
      (insertFixupRightRight
        (node Color.black a w (node Color.red b x (node Color.red c y d)))) := by
  simpa [insertFixupRightRight] using
    redBlackShape_black_with_red_children
      (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
      ha hb hc hd hab hbc hcd

/-- Unified local certificate for the left-left insertion-fixup branch. -/
theorem insertFixupLocal_leftLeft_certificate
    (q : Nat) {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    InsertFixupLocalCertificate q
      (node Color.black (node Color.red (node Color.red a w b) x c) y d)
      (insertFixupLocal InsertFixupCase.leftLeft
        (node Color.black (node Color.red (node Color.red a w b) x c) y d)) := by
  exact ⟨
    by
      simpa [insertFixupLocal] using
        inTree_insertFixup_leftLeft_iff q a b c d w x y,
    by
      simpa [insertFixupLocal] using
        blackHeight_insertFixup_leftLeft a b c d w x y,
    by
      simpa [insertFixupLocal] using
        redBlackShape_insertFixup_leftLeft
          (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
          ha hb hc hd hab hbc hcd
  ⟩

/-- Unified local certificate for the left-right insertion-fixup branch. -/
theorem insertFixupLocal_leftRight_certificate
    (q : Nat) {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    InsertFixupLocalCertificate q
      (node Color.black (node Color.red a w (node Color.red b x c)) y d)
      (insertFixupLocal InsertFixupCase.leftRight
        (node Color.black (node Color.red a w (node Color.red b x c)) y d)) := by
  exact ⟨
    by
      simpa [insertFixupLocal] using
        inTree_insertFixup_leftRight_iff q a b c d w x y,
    by
      simpa [insertFixupLocal] using
        blackHeight_insertFixup_leftRight a b c d w x y,
    by
      simpa [insertFixupLocal] using
        redBlackShape_insertFixup_leftRight
          (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
          ha hb hc hd hab hbc hcd
  ⟩

/-- Unified local certificate for the right-left insertion-fixup branch. -/
theorem insertFixupLocal_rightLeft_certificate
    (q : Nat) {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    InsertFixupLocalCertificate q
      (node Color.black a w (node Color.red (node Color.red b x c) y d))
      (insertFixupLocal InsertFixupCase.rightLeft
        (node Color.black a w (node Color.red (node Color.red b x c) y d))) := by
  exact ⟨
    by
      simpa [insertFixupLocal] using
        inTree_insertFixup_rightLeft_iff q a b c d w x y,
    by
      simpa [insertFixupLocal] using
        blackHeight_insertFixup_rightLeft a b c d w x y,
    by
      simpa [insertFixupLocal] using
        redBlackShape_insertFixup_rightLeft
          (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
          ha hb hc hd hab hbc hcd
  ⟩

/-- Unified local certificate for the right-right insertion-fixup branch. -/
theorem insertFixupLocal_rightRight_certificate
    (q : Nat) {a b c d : RBTree} {w x y : Nat}
    (ha : RedBlackShape a) (hb : RedBlackShape b)
    (hc : RedBlackShape c) (hd : RedBlackShape d)
    (hab : blackHeight a = blackHeight b)
    (hbc : blackHeight b = blackHeight c)
    (hcd : blackHeight c = blackHeight d) :
    InsertFixupLocalCertificate q
      (node Color.black a w (node Color.red b x (node Color.red c y d)))
      (insertFixupLocal InsertFixupCase.rightRight
        (node Color.black a w (node Color.red b x (node Color.red c y d)))) := by
  exact ⟨
    by
      simpa [insertFixupLocal] using
        inTree_insertFixup_rightRight_iff q a b c d w x y,
    by
      simpa [insertFixupLocal] using
        blackHeight_insertFixup_rightRight a b c d w x y,
    by
      simpa [insertFixupLocal] using
        redBlackShape_insertFixup_rightRight
          (a := a) (b := b) (c := c) (d := d) (w := w) (x := x) (y := y)
          ha hb hc hd hab hbc hcd
  ⟩

/-! **Red-rooted and weak red-black invariants for insertion** -/

/-- A red-rooted red-black subtree has no red-red edges and balanced black heights. -/
def RedRootedRB (t : RBTree) : Prop := NoRedRed t ∧ BalancedBlackHeight t

/-- Empty tree satisfies the red-black shape invariant. -/
theorem redBlackShape_empty : RedBlackShape empty := by
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]

/-- Build a black-rooted shape from two red-black shaped children. -/
theorem redBlackShape_node_black {l y r} (hL : RedBlackShape l) (hR : RedBlackShape r)
    (hHeight : blackHeight l = blackHeight r) :
    RedBlackShape (node Color.black l y r) := by
  rcases hL with ⟨_, hNoRedL, hBalL⟩
  rcases hR with ⟨_, hNoRedR, hBalR⟩
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]
  exact ⟨⟨hNoRedL, hNoRedR⟩, ⟨hBalL, hBalR, hHeight⟩⟩

/-- Build a black-rooted shape from two red-rooted children. -/
theorem redBlackShape_node_black_of_redRootedRB {l y r}
    (hL : RedRootedRB l) (hR : RedRootedRB r) (hHeight : blackHeight l = blackHeight r) :
    RedBlackShape (node Color.black l y r) := by
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]
  exact ⟨⟨hL.1, hR.1⟩, ⟨hL.2, hR.2, hHeight⟩⟩

/-- Build a black-rooted shape from a red-rooted left child and a shaped right child. -/
theorem redBlackShape_node_black_of_redRootedRB_right {l y r}
    (hL : RedBlackShape l) (hR : RedRootedRB r) (hHeight : blackHeight l = blackHeight r) :
    RedBlackShape (node Color.black l y r) := by
  rcases hL with ⟨_, hNoRedL, hBalL⟩
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]
  exact ⟨⟨hNoRedL, hR.1⟩, ⟨hBalL, hR.2, hHeight⟩⟩

/-- Build a black-rooted shape from a shaped left child and a red-rooted right child. -/
theorem redBlackShape_node_black_of_redRootedRB_left {l y r}
    (hL : RedRootedRB l) (hR : RedBlackShape r) (hHeight : blackHeight l = blackHeight r) :
    RedBlackShape (node Color.black l y r) := by
  rcases hR with ⟨_, hNoRedR, hBalR⟩
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight]
  exact ⟨⟨hL.1, hNoRedR⟩, ⟨hL.2, hBalR, hHeight⟩⟩

/-- Build a red-rooted black node from two red-rooted children. -/
theorem redRootedRB_node_black {l y r} (hL : RedRootedRB l) (hR : RedRootedRB r)
    (hHeight : blackHeight l = blackHeight r) :
    RedRootedRB (node Color.black l y r) := by
  simp [RedRootedRB, NoRedRed, BalancedBlackHeight]
  exact ⟨⟨hL.1, hR.1⟩, ⟨hL.2, hR.2, hHeight⟩⟩

/-- Build a red-rooted red node from two red-black shaped children. -/
theorem redRootedRB_node_red {l y r} (hL : RedBlackShape l) (hR : RedBlackShape r)
    (hHeight : blackHeight l = blackHeight r) :
    RedRootedRB (node Color.red l y r) := by
  rcases hL with ⟨hRootL, hNoRedL, hBalL⟩
  rcases hR with ⟨hRootR, hNoRedN, hBalR⟩
  simp [RedRootedRB, NoRedRed, BalancedBlackHeight, RootBlack]
  exact ⟨⟨hNoRedL, hNoRedN, hRootL, hRootR⟩, ⟨hBalL, hBalR, hHeight⟩⟩

/-- Children of a red-rooted node are red-rooted. -/
theorem redRootedRB_children {c l y r} (h : RedRootedRB (node c l y r)) :
    RedRootedRB l ∧ RedRootedRB r := by
  rcases h with ⟨hNoRed, hBal⟩
  simp [RedRootedRB, NoRedRed, BalancedBlackHeight] at hNoRed hBal ⊢
  exact ⟨⟨hNoRed.1, hBal.1⟩, ⟨hNoRed.2.1, hBal.2.1⟩⟩

/--
A weak red-black invariant: either the tree is red-rooted, or it has a single
red-red edge at the root (left or right orientation).
-/
def WeakRB (t : RBTree) : Prop :=
  RedRootedRB t ∨
    (∃ ll x lr y r,
      t = node Color.red (node Color.red ll x lr) y r ∧
        RedBlackShape ll ∧ RedBlackShape lr ∧ blackHeight ll = blackHeight lr ∧
        RedBlackShape r ∧ blackHeight ll = blackHeight r) ∨
    (∃ l y rl x rr,
      t = node Color.red l y (node Color.red rl x rr) ∧
        RedBlackShape l ∧ RedBlackShape rl ∧ RedBlackShape rr ∧
        blackHeight rl = blackHeight rr ∧ blackHeight rl = blackHeight l)

/-- Constructor for the red-rooted disjunct of {name}`WeakRB`. -/
theorem WeakRB.redRooted {t : RBTree} (h : RedRootedRB t) : WeakRB t :=
  Or.inl h

/-- Constructor for the left red-red disjunct of {name}`WeakRB`. -/
theorem WeakRB.red_left {ll x lr y r}
    (hLL : RedBlackShape ll) (hLR : RedBlackShape lr)
    (hEqLL : blackHeight ll = blackHeight lr) (hRR : RedBlackShape r)
    (hEqR : blackHeight ll = blackHeight r) :
    WeakRB (node Color.red (node Color.red ll x lr) y r) :=
  Or.inr (Or.inl ⟨ll, x, lr, y, r, rfl, hLL, hLR, hEqLL, hRR, hEqR⟩)

/-- Constructor for the right red-red disjunct of {name}`WeakRB`. -/
theorem WeakRB.red_right {l y rl x rr}
    (hL : RedBlackShape l) (hRL : RedBlackShape rl) (hRR : RedBlackShape rr)
    (hEqRL : blackHeight rl = blackHeight rr) (hEqL : blackHeight rl = blackHeight l) :
    WeakRB (node Color.red l y (node Color.red rl x rr)) :=
  Or.inr (Or.inr ⟨l, y, rl, x, rr, rfl, hL, hRL, hRR, hEqRL, hEqL⟩)

/-- Every red-rooted tree is weakly red-black. -/
theorem redRootedRB_weakRB {t : RBTree} (h : RedRootedRB t) : WeakRB t :=
  WeakRB.redRooted h

/-- A red-black shaped tree is red-rooted. -/
theorem redBlackShape_redRootedRB {t : RBTree} (h : RedBlackShape t) : RedRootedRB t :=
  ⟨h.2.1, h.2.2⟩

/-- Repainting a red-rooted tree black yields a red-black shaped tree. -/
theorem redBlackShape_repaintRoot_black_of_redRootedRB {t : RBTree} (h : RedRootedRB t) :
    RedBlackShape (repaintRoot Color.black t) := by
  cases t with
  | empty => exact redBlackShape_empty
  | node c l y r =>
      rcases h with ⟨hNoRed, hBal⟩
      have hChildren := redRootedRB_children (show RedRootedRB (node c l y r) by exact ⟨hNoRed, hBal⟩)
      cases c with
      | black =>
          exact redBlackShape_node_black_of_redRootedRB hChildren.1 hChildren.2 hBal.2.2
      | red =>
          have hRoots := hNoRed.2.2 (by rfl)
          have hRootL := hRoots.1
          have hRootR := hRoots.2
          have hShapeL : RedBlackShape l := ⟨hRootL, hChildren.1.1, hChildren.1.2⟩
          have hShapeR : RedBlackShape r := ⟨hRootR, hChildren.2.1, hChildren.2.2⟩
          exact redBlackShape_node_black_of_redRootedRB_left hChildren.1 hShapeR hBal.2.2

/-- Repainting a weakly red-black tree black yields a red-black shaped tree. -/
theorem redBlackShape_repaintRoot_black_of_weakRB {t : RBTree} (h : WeakRB t) :
    RedBlackShape (repaintRoot Color.black t) := by
  rcases h with h | ⟨ll, kx, lr, weakY, rr, rfl, hLL, hLR, hEqLL, hRR, hEqR⟩ | ⟨lL, weakY, rl, kx, rr, rfl, hLShape, hRL, hRR, hEqRL, hEqL⟩
  · exact redBlackShape_repaintRoot_black_of_redRootedRB h
  · simp [repaintRoot]
    exact redBlackShape_node_black_of_redRootedRB_left
      (redRootedRB_node_red hLL hLR hEqLL)
      hRR
      (by simp [blackHeight, hEqR])
  · simp [repaintRoot]
    exact redBlackShape_node_black_of_redRootedRB_right
      hLShape
      (redRootedRB_node_red hRL hRR hEqRL)
      (by simp [blackHeight, hEqL])

/-! **Okasaki-style single-step balance** -/

/-- Rebalance after insertion on the left child. -/
def balanceLeft (l : RBTree) (y : Nat) (r : RBTree) : RBTree :=
  match l with
  | node Color.red (node Color.red a w b) x c =>
      node Color.red (node Color.black a w b) x (node Color.black c y r)
  | node Color.red a w (node Color.red b x c) =>
      node Color.red (node Color.black a w b) x (node Color.black c y r)
  | _ => node Color.black l y r

/-- Rebalance after insertion on the right child. -/
def balanceRight (l : RBTree) (y : Nat) (r : RBTree) : RBTree :=
  match r with
  | node Color.red (node Color.red b x c) y' d =>
      node Color.red (node Color.black l y b) x (node Color.black c y' d)
  | node Color.red b x (node Color.red c y' d) =>
      node Color.red (node Color.black l y b) x (node Color.black c y' d)
  | _ => node Color.black l y r

/-- {lit}`balanceLeft` preserves membership. -/
theorem inTree_balanceLeft_iff (q : Nat) (l : RBTree) (y : Nat) (r : RBTree) :
    InTree q (balanceLeft l y r) ↔ InTree q (node Color.black l y r) := by
  unfold balanceLeft
  split
  · simp [InTree, or_assoc, or_left_comm]
  · rename_i hneg
    simp [InTree, or_assoc, or_left_comm]
  · rfl

/-- {lit}`balanceRight` preserves membership. -/
theorem inTree_balanceRight_iff (q : Nat) (l : RBTree) (y : Nat) (r : RBTree) :
    InTree q (balanceRight l y r) ↔ InTree q (node Color.black l y r) := by
  unfold balanceRight
  split
  · simp [InTree, or_assoc, or_left_comm]
  · rename_i hneg
    simp [InTree, or_assoc, or_left_comm]
  · rfl

/-- {lit}`balanceLeft` preserves the black height of the surrounding black node. -/
theorem blackHeight_balanceLeft {l y r} :
    blackHeight (balanceLeft l y r) = blackHeight (node Color.black l y r) := by
  unfold balanceLeft
  split <;> simp [blackHeight]

/-- {lit}`balanceRight` preserves the black height of the surrounding black node. -/
theorem blackHeight_balanceRight {l y r} :
    blackHeight (balanceRight l y r) = blackHeight (node Color.black l y r) := by
  unfold balanceRight
  split <;> simp [blackHeight]

/-- Children of a red-rooted red node are red-black shaped. -/
theorem redBlackShape_children_of_redRootedRB_red {ll x lr}
    (h : RedRootedRB (node Color.red ll x lr)) :
    RedBlackShape ll ∧ RedBlackShape lr := by
  rcases h with ⟨hNoRed, hBal⟩
  simp [RedBlackShape, RootBlack, NoRedRed, BalancedBlackHeight] at hNoRed hBal ⊢
  exact ⟨⟨hNoRed.2.2.1, hNoRed.1, hBal.1⟩, ⟨hNoRed.2.2.2, hNoRed.2.1, hBal.2.1⟩⟩

/-- A red node whose children are red-rooted/shaped is weakly red-black. -/
theorem weakRB_red_node_left {l y r} (hL : RedRootedRB l) (hR : RedBlackShape r)
    (hHeight : blackHeight l = blackHeight r) :
    WeakRB (node Color.red l y r) := by
  cases l with
  | empty =>
      exact WeakRB.redRooted (redRootedRB_node_red redBlackShape_empty hR hHeight)
  | node c ll lx lr =>
      cases c with
      | black =>
          have hShapeL : RedBlackShape (node Color.black ll lx lr) :=
            ⟨by simp [RootBlack], hL.1, hL.2⟩
          exact WeakRB.redRooted (redRootedRB_node_red hShapeL hR hHeight)
      | red =>
          have hChildren := redBlackShape_children_of_redRootedRB_red hL
          have hNoRed := hL.1
          have hBal := hL.2
          simp [NoRedRed, BalancedBlackHeight] at hNoRed hBal
          have hEqLL : blackHeight ll = blackHeight lr := hBal.2.2
          have hEqL : blackHeight ll = blackHeight r := by
            simp [blackHeight, hEqLL] at hHeight ⊢; exact hHeight
          exact WeakRB.red_left hChildren.1 hChildren.2 hEqLL hR hEqL

/-- Symmetric: a red node whose children are shaped/red-rooted is weakly red-black. -/
theorem weakRB_red_node_right {l y r} (hL : RedBlackShape l) (hR : RedRootedRB r)
    (hHeight : blackHeight l = blackHeight r) :
    WeakRB (node Color.red l y r) := by
  cases r with
  | empty =>
      exact WeakRB.redRooted (redRootedRB_node_red hL redBlackShape_empty hHeight)
  | node c rl yr rr =>
      cases c with
      | black =>
          have hShapeR : RedBlackShape (node Color.black rl yr rr) :=
            ⟨by simp [RootBlack], hR.1, hR.2⟩
          exact WeakRB.redRooted (redRootedRB_node_red hL hShapeR hHeight)
      | red =>
          have hChildren := redBlackShape_children_of_redRootedRB_red hR
          have hNoRed := hR.1
          have hBal := hR.2
          simp [NoRedRed, BalancedBlackHeight] at hNoRed hBal
          have hEqRR : blackHeight rl = blackHeight rr := hBal.2.2
          have hEqR : blackHeight rl = blackHeight l := by
            simp [blackHeight, hEqRR] at hHeight ⊢; exact hHeight.symm
          exact WeakRB.red_right hL hChildren.1 hChildren.2 hEqRR hEqR

/-- {lit}`balanceLeft` turns a weak left child into a red-rooted node. -/
theorem redRootedRB_balanceLeft {l y r} (hL : WeakRB l) (hR : RedRootedRB r)
    (hHeight : blackHeight l = blackHeight r) :
    RedRootedRB (balanceLeft l y r) := by
  rcases hL with hL | ⟨ll, kx, lr, weakY, rr, rfl, hLL, hLR, hEqLL, hRR, hEqR⟩ | ⟨lL, weakY, rl, kx, rr, rfl, hLShape, hRL, hRR, hEqRL, hEqL⟩
  · unfold balanceLeft
    split
    · exfalso
      simp [RedRootedRB, NoRedRed, RootBlack] at hL
    · exfalso
      simp [RedRootedRB, NoRedRed, RootBlack] at hL
    · exact redRootedRB_node_black hL hR hHeight
  · have hEqHeightRR : blackHeight rr = blackHeight r := by
      have h1 : blackHeight (node Color.red (node Color.red ll kx lr) weakY rr) = blackHeight ll := by simp [blackHeight]
      omega
    simp [balanceLeft]
    exact redRootedRB_node_red (redBlackShape_node_black hLL hLR hEqLL)
      (redBlackShape_node_black_of_redRootedRB_right hRR hR hEqHeightRR)
      (by simp [blackHeight, hEqR])
  · unfold balanceLeft
    split
    · -- first pattern impossible because lL root black
      rename_i heq
      cases heq
      simp [RedBlackShape, RootBlack] at hLShape
    · -- second pattern matches
      rename_i hneg heq
      cases heq
      have hEqHeightRR : blackHeight rr = blackHeight r := by
        have h1 : blackHeight (node Color.red lL weakY (node Color.red rl kx rr)) = blackHeight lL := by simp [blackHeight]
        omega
      exact redRootedRB_node_red
        (redBlackShape_node_black hLShape hRL (by omega))
        (redBlackShape_node_black_of_redRootedRB_right hRR hR hEqHeightRR)
        (by simp [blackHeight]; omega)
    · -- default impossible because l matches second pattern
      rename_i hneg1 hneg2
      exfalso
      apply hneg2 lL weakY rl kx rr; rfl

/-- {lit}`balanceRight` turns a weak right child into a red-rooted node. -/
theorem redRootedRB_balanceRight {l y r} (hL : RedRootedRB l) (hR : WeakRB r)
    (hHeight : blackHeight l = blackHeight r) :
    RedRootedRB (balanceRight l y r) := by
  rcases hR with hR | ⟨ll, kx, lr, weakY, rr, rfl, hLL, hLR, hEqLL, hRR, hEqR⟩ | ⟨rL, weakY, rl, kx, rr, rfl, hRShape, hRL, hRR, hEqRL, hEqR⟩
  · unfold balanceRight
    split
    · exfalso
      simp [RedRootedRB, NoRedRed, RootBlack] at hR
    · exfalso
      simp [RedRootedRB, NoRedRed, RootBlack] at hR
    · exact redRootedRB_node_black hL hR hHeight
  · unfold balanceRight
    split
    · -- first pattern matches
      rename_i heq
      cases heq
      have hEqHeightLL : blackHeight l = blackHeight ll := by
        have h1 : blackHeight (node Color.red (node Color.red ll kx lr) weakY rr) = blackHeight ll := by simp [blackHeight]
        omega
      exact redRootedRB_node_red
        (redBlackShape_node_black_of_redRootedRB_left hL hLL hEqHeightLL)
        (redBlackShape_node_black hLR hRR (by omega))
        (by simp [blackHeight]; omega)
    · -- second pattern impossible because rr is a red node
      rename_i hneg heq
      cases heq
      simp [RedBlackShape, RootBlack] at hRR
    · -- default impossible because r matches first pattern
      rename_i hneg1 hneg2
      exfalso
      apply hneg1 ll kx lr weakY rr; rfl
  · unfold balanceRight
    split
    · -- first pattern impossible because rL root black
      rename_i heq
      cases heq
      simp [RedBlackShape, RootBlack] at hRShape
    · -- second pattern matches
      rename_i hneg heq
      cases heq
      have hEqHeightL : blackHeight l = blackHeight rL := by
        have h1 : blackHeight (node Color.red rL weakY (node Color.red rl kx rr)) = blackHeight rL := by simp [blackHeight]
        omega
      exact redRootedRB_node_red
        (redBlackShape_node_black_of_redRootedRB_left hL hRShape hEqHeightL)
        (redBlackShape_node_black hRL hRR hEqRL)
        (by simp [blackHeight]; omega)
    · -- default impossible because r matches second pattern
      rename_i hneg1 hneg2
      exfalso
      apply hneg2 rL weakY rl kx rr; rfl

/-! **Executable insertion** -/

/-- Insertion fixup: recurses down the tree and rebalances on the way back up. -/
def insertFixup (x : Nat) : RBTree → RBTree
  | empty => node Color.red empty x empty
  | node c l y r =>
      if x < y then
        if c = Color.black then balanceLeft (insertFixup x l) y r
        else node Color.red (insertFixup x l) y r
      else if x > y then
        if c = Color.black then balanceRight l y (insertFixup x r)
        else node Color.red l y (insertFixup x r)
      else node c l y r

/-- Insert a key into a red-black tree and repaint the root black. -/
def insert (x : Nat) (t : RBTree) : RBTree :=
  repaintRoot Color.black (insertFixup x t)

/-- {lit}`insertFixup` preserves membership. -/
theorem inTree_insertFixup_iff (x y : Nat) (t : RBTree) :
    InTree y (insertFixup x t) ↔ y = x ∨ InTree y t := by
  induction t with
  | empty => simp [insertFixup, InTree]
  | node c l z r ihl ihr =>
      simp [insertFixup]
      by_cases h1 : x < z
      · simp [h1]
        by_cases hc : c = Color.black
        · simp [hc, inTree_balanceLeft_iff]
          simp [InTree, ihl]
          tauto
        · have hc' : c = Color.red := by cases c <;> tauto
          simp [hc', InTree, ihl]
          tauto
      · by_cases h2 : x > z
        · simp [h1, h2]
          by_cases hc : c = Color.black
          · simp [hc, inTree_balanceRight_iff]
            simp [InTree, ihr]
            tauto
          · have hc' : c = Color.red := by cases c <;> tauto
            simp [hc', InTree, ihr]
            tauto
        · have h3 : x = z := by omega
          simp [h3, InTree]
          try tauto

/-- {lit}`insert` preserves membership. -/
theorem inTree_insert_iff (x y : Nat) (t : RBTree) :
    InTree y (insert x t) ↔ y = x ∨ InTree y t := by
  simp [insert, inTree_insertFixup_iff, inTree_repaintRoot_iff]

/-- The central recursion invariant for {lit}`insertFixup`. -/
theorem insertFixup_invariant {x : Nat} {t : RBTree} (h : RedRootedRB t) :
    WeakRB (insertFixup x t) ∧
      blackHeight (insertFixup x t) = blackHeight t ∧
      (RootBlack t → RedRootedRB (insertFixup x t)) := by
  induction t with
  | empty =>
      exact ⟨redRootedRB_weakRB (by simp [insertFixup, RedRootedRB, NoRedRed, BalancedBlackHeight, RootBlack]),
        by simp [insertFixup, blackHeight],
        by simp [RootBlack, insertFixup, RedRootedRB, NoRedRed, BalancedBlackHeight]⟩
  | node c l y r ihl ihr =>
      have hNoRed := h.1
      have hBalanced := h.2
      rcases hNoRed with ⟨hNoRedL, hNoRedR, hColor⟩
      rcases hBalanced with ⟨hBalL, hBalR, hEqHeight⟩
      have hRootedL : RedRootedRB l := ⟨hNoRedL, hBalL⟩
      have hRootedR : RedRootedRB r := ⟨hNoRedR, hBalR⟩
      have ihL := ihl hRootedL
      have ihR := ihr hRootedR
      simp [insertFixup]
      by_cases h1 : x < y
      · simp [h1]
        by_cases hc : c = Color.black
        · simp [hc]
          have hRooted : RedRootedRB (balanceLeft (insertFixup x l) y r) :=
            redRootedRB_balanceLeft ihL.1 hRootedR (by rw [ihL.2.1, hEqHeight])
          exact ⟨redRootedRB_weakRB hRooted,
            by rw [blackHeight_balanceLeft]; simp [blackHeight]; try omega,
            fun _ => hRooted⟩
        · have hc' : c = Color.red := by cases c <;> tauto
          simp [hc']
          have hRootL : RootBlack l := (hColor hc').1
          have hRootedL' := ihL.2.2 hRootL
          have hRootR : RootBlack r := (hColor hc').2
          have hShapeR : RedBlackShape r := ⟨hRootR, hNoRedR, hBalR⟩
          have hWeak := weakRB_red_node_left (y := y) hRootedL' hShapeR (by rw [ihL.2.1, hEqHeight])
          exact ⟨hWeak,
            by simp [blackHeight]; try omega,
            by simp [RootBlack]⟩
      · by_cases h2 : x > y
        · simp [h1, h2]
          by_cases hc : c = Color.black
          · simp [hc]
            have hRooted : RedRootedRB (balanceRight l y (insertFixup x r)) :=
              redRootedRB_balanceRight hRootedL ihR.1 (by rw [ihR.2.1, hEqHeight])
            exact ⟨redRootedRB_weakRB hRooted,
              by rw [blackHeight_balanceRight]; simp [blackHeight]; try omega,
              fun _ => hRooted⟩
          · have hc' : c = Color.red := by cases c <;> tauto
            simp [hc']
            have hRootL : RootBlack l := (hColor hc').1
            have hRootR : RootBlack r := (hColor hc').2
            have hRootedR' := ihR.2.2 hRootR
            have hShapeL : RedBlackShape l := ⟨hRootL, hNoRedL, hBalL⟩
            have hWeak := weakRB_red_node_right (y := y) hShapeL hRootedR' (by rw [ihR.2.1, hEqHeight])
            exact ⟨hWeak,
              by simp [blackHeight]; try omega,
              by simp [RootBlack]⟩
        · have h3 : x = y := by omega
          rw [if_neg h1, if_neg h2]
          exact ⟨redRootedRB_weakRB h, by simp [blackHeight], fun _ => h⟩

/-- Insertion preserves red-black shape. -/
theorem redBlackShape_insert {x : Nat} {t : RBTree} (h : RedBlackShape t) :
    RedBlackShape (insert x t) := by
  have hInv := @insertFixup_invariant x t (redBlackShape_redRootedRB h)
  exact redBlackShape_repaintRoot_black_of_weakRB hInv.1

/-- {lit}`insertFixup` preserves the original black height. -/
theorem blackHeight_insertFixup {x : Nat} {t : RBTree} (h : RedBlackShape t) :
    blackHeight (insertFixup x t) = blackHeight t := by
  have hInv := @insertFixup_invariant x t (redBlackShape_redRootedRB h)
  exact hInv.2.1

/-- Repainting an already-black root does not change black height. -/
theorem blackHeight_repaintRoot_black_same {t : RBTree} (h : RootBlack t) :
    blackHeight (repaintRoot Color.black t) = blackHeight t := by
  cases t with
  | empty => simp [repaintRoot, blackHeight]
  | node c l y r =>
      simp [RootBlack] at h
      simp [repaintRoot, blackHeight, h]

/-- Repainting a red root increases black height by one. -/
theorem blackHeight_repaintRoot_black_increases {t : RBTree} (h : ¬ RootBlack t) :
    blackHeight (repaintRoot Color.black t) = blackHeight t + 1 := by
  cases t with
  | empty => simp [RootBlack] at h
  | node c l y r =>
      simp [RootBlack] at h
      have hc : c = Color.red := by cases c <;> tauto
      simp [repaintRoot, blackHeight, hc]

/-- Insertion either keeps the black height or increases it by one. -/
theorem blackHeight_insert {x : Nat} {t : RBTree} (h : RedBlackShape t) :
    blackHeight (insert x t) = blackHeight t ∨ blackHeight (insert x t) = blackHeight t + 1 := by
  have hInv := @insertFixup_invariant x t (redBlackShape_redRootedRB h)
  have hHeight : blackHeight (insertFixup x t) = blackHeight t := hInv.2.1
  by_cases hRoot : RootBlack (insertFixup x t)
  · left
    rw [insert]
    rw [blackHeight_repaintRoot_black_same hRoot, hHeight]
  · right
    rw [insert]
    rw [blackHeight_repaintRoot_black_increases hRoot, hHeight]
/-! ## Logarithmic height bound (CLRS Lemma 13.1)

A red-black tree with {lit}`n` internal nodes has height at most
{lit}`2 log₂(n + 1)`.  The proof follows the textbook decomposition:

1. Every subtree rooted at {lit}`x` has at least {lit}`2^{bh(x)} - 1` internal
   nodes (Lemma A).
2. The height of a no-red-red tree is at most twice its black height (Lemma B).
3. From (1), {lit}`bh ≤ log₂(n + 1)`; from (2), {lit}`h ≤ 2·bh`.

Main results:

- Theorem {lit}`height_le_two_mul_blackHeight_of_RedBlackShape`: height ≤ 2·bh
  for any red-black-shaped tree.
- Theorem {lit}`size_add_one_ge_two_pow_blackHeight`: size + 1 ≥ 2^bh for any
  balanced-black-height tree.
- Theorem {lit}`height_log_bound`: the full CLRS Lemma 13.1 bound. -/

/-- The height (maximum depth) of a red-black tree: the longest path from the
root to an empty leaf, counting edges.  Empty tree height is 0. -/
def height : RBTree → Nat
  | .empty => 0
  | .node _ l _ r => 1 + max l.height r.height

/-- The internal node count of a red-black tree. -/
def size : RBTree → Nat
  | .empty => 0
  | .node _ l _ r => 1 + l.size + r.size

/-- **Lemma A.**  A tree with balanced black heights has at least {lit}`2^{bh} - 1`
internal nodes.  Formalised as {lit}`size t + 1 ≥ 2 ^ blackHeight t`. -/
theorem size_add_one_ge_two_pow_blackHeight (t : RBTree)
    (hBal : BalancedBlackHeight t) : size t + 1 ≥ 2 ^ blackHeight t := by
  induction t with
  | empty => simp [size, blackHeight]
  | node c l k r ihl ihr =>
    simp only [BalancedBlackHeight] at hBal
    rcases hBal with ⟨hlBal, hrBal, heq⟩
    have ihl' : size l + 1 ≥ 2 ^ blackHeight l := ihl hlBal
    have ihr' : size r + 1 ≥ 2 ^ blackHeight l := by
      rw [heq]; exact ihr hrBal
    simp only [size]
    have h_sum : 1 + size l + size r + 1 = (size l + 1) + (size r + 1) := by omega
    rw [h_sum]
    rw [blackHeight]
    have h_pow_succ : 2 ^ blackHeight l + 2 ^ blackHeight l = 2 ^ (blackHeight l + 1) := by
      rw [← two_mul, mul_comm, ← Nat.pow_succ 2 (blackHeight l)]
    by_cases hc : c = Color.black
    · subst hc
      have h_if : (if Color.black = Color.black then (1 : ℕ) else 0) = 1 := by simp
      rw [h_if]
      rw [← h_pow_succ]
      exact add_le_add ihl' ihr'
    · -- c ≠ black
      rw [if_neg hc]
      have h_add : (size l + 1) + (size r + 1) ≥ size l + 1 := Nat.le_add_right _ _
      exact Nat.le_trans ihl' h_add

/-- **Boolean root-black test**, for use in propositions that need decidability. -/
def rootBlack : RBTree → Bool
  | .empty => true
  | .node c _ _ _ => c = Color.black

/-- The {lit}`Bool` version agrees with the {lit}`Prop` version. -/
theorem rootBlack_eq_RootBlack (t : RBTree) : rootBlack t = true ↔ RootBlack t := by
  cases t <;> simp [rootBlack, RootBlack]

/-- **Lemma B (strengthened induction hypothesis).**  For a tree with
{lit}`NoRedRed` and {lit}`BalancedBlackHeight`, the height is bounded by twice
the black height plus a root-color adjustment term.  Uses a {lit}`Bool` version
of the condition to avoid decidability issues. -/
theorem height_le_two_mul_blackHeight_add_adj (t : RBTree)
    (hRed : NoRedRed t) (hBal : BalancedBlackHeight t) :
    height t ≤ 2 * blackHeight t + (if rootBlack t then 0 else 1) := by
  induction t with
  | empty => simp [height, blackHeight, rootBlack]
  | node c l k r ihl ihr =>
    simp only [NoRedRed] at hRed
    rcases hRed with ⟨hlRed, hrRed, hRedCond⟩
    simp only [BalancedBlackHeight] at hBal
    rcases hBal with ⟨hlBal, hrBal, heq⟩
    have ihl' := ihl hlRed hlBal
    have ihr' := ihr hrRed hrBal
    simp only [height, blackHeight]
    have hmax : max (height l) (height r) ≤ 2 * blackHeight l + 1 := by
      have hL : height l ≤ 2 * blackHeight l + (if rootBlack l then 0 else 1) := ihl'
      have hR : height r ≤ 2 * blackHeight r + (if rootBlack r then 0 else 1) := ihr'
      have hR' : height r ≤ 2 * blackHeight l + (if rootBlack r then 0 else 1) := by
        rw [heq]; exact hR
      have adjL : (if rootBlack l then 0 else 1 : ℕ) ≤ 1 := by split <;> omega
      have adjR : (if rootBlack r then 0 else 1 : ℕ) ≤ 1 := by split <;> omega
      apply max_le
      · omega
      · omega
    have hrhs : 1 + max (height l) (height r) ≤ 1 + (2 * blackHeight l + 1) := by omega
    by_cases hc : c = Color.black
    · subst hc
      simp
      convert Nat.add_le_add_right hmax 1 using 1
      · simp [add_comm]
      · calc
          (2 * blackHeight l + 1) + 1 = 2 * blackHeight l + (1 + 1) := by rw [add_assoc]
          _ = 2 * blackHeight l + 2 := by norm_num
          _ = 2 * (blackHeight l + 1) := by rw [Nat.mul_succ]
    · have hc_red : c = Color.red := by cases c <;> simp_all
      subst hc_red
      simp
      have hmax_red : max (height l) (height r) ≤ 2 * blackHeight l := by
        have hl_bound : height l ≤ 2 * blackHeight l := by
          -- From ihl': height l ≤ 2*bl + (if rootBlack l then 0 else 1)
          -- After subst, rootBlack l = true (from NoRedRed)
          have hRoot_lb : rootBlack l = true :=
            (rootBlack_eq_RootBlack l).mpr ((hRedCond rfl).1)
          simp [hRoot_lb] at ihl'; omega
        have hr_bound : height r ≤ 2 * blackHeight l := by
          have hRoot_rb : rootBlack r = true :=
            (rootBlack_eq_RootBlack r).mpr ((hRedCond rfl).2)
          simp [hRoot_rb] at ihr'; omega
        exact max_le hl_bound hr_bound
      convert Nat.add_le_add_right hmax_red 1 using 1
      · simp [add_comm]
      · rfl

/-- **Lemma B (public form).**  For any red-black-shaped tree, height ≤ 2·bh. -/
theorem height_le_two_mul_blackHeight_of_RedBlackShape (t : RBTree)
    (hShape : RedBlackShape t) : height t ≤ 2 * blackHeight t := by
  obtain ⟨hRoot, hRed, hBal⟩ := hShape
  have h := height_le_two_mul_blackHeight_add_adj t hRed hBal
  have hRoot_b : rootBlack t = true := (rootBlack_eq_RootBlack t).mpr hRoot
  rw [hRoot_b] at h
  simpa using h

/-- **CLRS Lemma 13.1.**  A red-black tree with {lit}`n` internal nodes has
height at most {lit}`2 log₂ (n + 1)`. -/
theorem height_log_bound (t : RBTree) (hShape : RedBlackShape t) :
    height t ≤ 2 * Nat.log 2 (size t + 1) := by
  have hBal : BalancedBlackHeight t := hShape.2.2
  have hSize := size_add_one_ge_two_pow_blackHeight t hBal
  have hHeight := height_le_two_mul_blackHeight_of_RedBlackShape t hShape
  have hLog : blackHeight t ≤ Nat.log 2 (size t + 1) :=
    Nat.le_log_of_pow_le (by omega) hSize
  omega

/-! ## Local deletion-fixup cases (CLRS RB-DELETE-FIXUP)

After deleting a black node the tree carries a *doubly-black* deficit: one
subtree has black height one less than its sibling.  {lit}`RB-DELETE-FIXUP` restores
balance through four local cases, mirrored below for the situation where the
deficient node is a *left* child (so its sibling {lit}`w` is the right child of the
parent).  Each case is a pure local rewrite; we prove that every case preserves
membership, and that the terminating Case 4 resolves the deficit and
re-establishes the no-red-red and balanced-black-height shape.

Main results:

- Definitions {lit}`deleteFixupCase1`..{lit}`deleteFixupCase4` and the {lit}`DeleteFixupCase`
  dispatcher {lit}`deleteFixupLocal`.
- Theorems {lit}`inTree_deleteFixupCase*_iff`: every case preserves membership.
- Theorem {lit}`deleteFixupCase4_shape`: the terminating rotation case restores the
  no-red-red and balanced invariants and fixes the black-height deficit. -/

/-- **Case 1** (sibling {lit}`w` is red): left-rotate the parent, recolour {lit}`w` black
and the parent red, exposing a black sibling for Cases 2-4. -/
def deleteFixupCase1 : RBTree → RBTree
  | node pc x pk (node Color.red wl wk wr) =>
      node pc (node Color.red x pk wl) wk wr
  | t => t

/-- **Case 2** ({lit}`w` black with two black children): recolour {lit}`w` red, pushing
the deficit up to the parent. -/
def deleteFixupCase2 : RBTree → RBTree
  | node pc x pk (node Color.black wl wk wr) =>
      node pc x pk (node Color.red wl wk wr)
  | t => t

/-- **Case 3** ({lit}`w` black, {lit}`w.left` red, {lit}`w.right` black): right-rotate {lit}`w` and
recolour, reducing to Case 4. -/
def deleteFixupCase3 : RBTree → RBTree
  | node pc x pk (node Color.black (node Color.red wll wlk wlr) wk wr) =>
      node pc x pk (node Color.black wll wlk (node Color.red wlr wk wr))
  | t => t

/-- **Case 4** ({lit}`w` black, {lit}`w.right` red): left-rotate the parent, recolour, and
the deficit is resolved. -/
def deleteFixupCase4 : RBTree → RBTree
  | node pc x pk (node Color.black wl wk (node Color.red wrl wrk wrr)) =>
      node pc (node Color.black x pk wl) wk (node Color.black wrl wrk wrr)
  | t => t

/-- The four local CLRS delete-fixup case orientations (deficient left child). -/
inductive DeleteFixupCase where
  | case1
  | case2
  | case3
  | case4
  deriving Repr, DecidableEq

/-- Unified dispatcher for the four local delete-fixup rewrites. -/
def deleteFixupLocal : DeleteFixupCase → RBTree → RBTree
  | DeleteFixupCase.case1, t => deleteFixupCase1 t
  | DeleteFixupCase.case2, t => deleteFixupCase2 t
  | DeleteFixupCase.case3, t => deleteFixupCase3 t
  | DeleteFixupCase.case4, t => deleteFixupCase4 t

/-- Case 1 preserves membership. -/
theorem inTree_deleteFixupCase1_iff (q : Nat) (x wl wr : RBTree) (pk wk : Nat)
    (pc : Color) :
    InTree q (deleteFixupCase1 (node pc x pk (node Color.red wl wk wr))) ↔
      InTree q (node pc x pk (node Color.red wl wk wr)) := by
  simp [deleteFixupCase1, InTree, or_assoc, or_left_comm]

/-- Case 2 preserves membership. -/
theorem inTree_deleteFixupCase2_iff (q : Nat) (x wl wr : RBTree) (pk wk : Nat)
    (pc : Color) :
    InTree q (deleteFixupCase2 (node pc x pk (node Color.black wl wk wr))) ↔
      InTree q (node pc x pk (node Color.black wl wk wr)) := by
  simp [deleteFixupCase2, InTree]

/-- Case 3 preserves membership. -/
theorem inTree_deleteFixupCase3_iff (q : Nat) (x wll wlr wr : RBTree)
    (pk wlk wk : Nat) (pc : Color) :
    InTree q (deleteFixupCase3
        (node pc x pk (node Color.black (node Color.red wll wlk wlr) wk wr))) ↔
      InTree q (node pc x pk (node Color.black (node Color.red wll wlk wlr) wk wr)) := by
  simp [deleteFixupCase3, InTree, or_assoc, or_left_comm]

/-- Case 4 preserves membership. -/
theorem inTree_deleteFixupCase4_iff (q : Nat) (x wl wrl wrr : RBTree)
    (pk wk wrk : Nat) (pc : Color) :
    InTree q (deleteFixupCase4
        (node pc x pk (node Color.black wl wk (node Color.red wrl wrk wrr)))) ↔
      InTree q (node pc x pk (node Color.black wl wk (node Color.red wrl wrk wrr))) := by
  simp [deleteFixupCase4, InTree, or_assoc, or_left_comm]

/-- **Case 4 terminating certificate.**  When the deficient left subtree {lit}`x` and
the sibling's fringe subtrees {lit}`wl`, {lit}`wrl`, {lit}`wrr` are red-black shaped with equal
black heights (the doubly-black deficit {lit}`blackHeight x = blackHeight wl`), the
left-rotation-and-recolour of Case 4 re-establishes the no-red-red and
balanced-black-height invariants — the deficit is resolved regardless of the
parent colour {lit}`pc`. -/
theorem deleteFixupCase4_shape
    {x wl wrl wrr : RBTree} {pk wk wrk : Nat} {pc : Color}
    (hx : RedBlackShape x) (hwl : RedBlackShape wl)
    (hwrl : RedBlackShape wrl) (hwrr : RedBlackShape wrr)
    (hxwl : blackHeight x = blackHeight wl)
    (hwlwrl : blackHeight wl = blackHeight wrl)
    (hwrlwrr : blackHeight wrl = blackHeight wrr) :
    NoRedRed (deleteFixupCase4
        (node pc x pk (node Color.black wl wk (node Color.red wrl wrk wrr)))) ∧
    BalancedBlackHeight (deleteFixupCase4
        (node pc x pk (node Color.black wl wk (node Color.red wrl wrk wrr)))) := by
  rcases hx with ⟨_hxRoot, hxNoRed, hxBal⟩
  rcases hwl with ⟨_hwlRoot, hwlNoRed, hwlBal⟩
  rcases hwrl with ⟨_hwrlRoot, hwrlNoRed, hwrlBal⟩
  rcases hwrr with ⟨_hwrrRoot, hwrrNoRed, hwrrBal⟩
  refine ⟨?_, ?_⟩
  · simp [deleteFixupCase4, NoRedRed, RootBlack]
    exact ⟨⟨hxNoRed, hwlNoRed⟩, hwrlNoRed, hwrrNoRed⟩
  · simp [deleteFixupCase4, BalancedBlackHeight]
    refine ⟨⟨hxBal, hwlBal, hxwl⟩, ⟨hwrlBal, hwrrBal, hwrlwrr⟩, ?_⟩
    simp only [blackHeight]
    omega

/-! ## Executable functional deletion (CLRS RB-DELETE)

This section develops the fully-composed executable red-black *deletion*
following the standard Okasaki/Kahrs functional-deletion pattern (as used in
Nipkow's verified `RBT_Set` development).  It reuses the insertion balancers
{lit}`balanceLeft` and {lit}`balanceRight` and adds the deletion re-balancers
{lit}`baldL` and {lit}`baldR`, the minimum-splicing {lit}`splitMin`, and the recursive
{lit}`del` / {lit}`delete`.

The invariant bookkeeping tracks two relaxations of the shape predicate:

- {lit}`NoRedRed2 t` (a weakened {lit}`NoRedRed`): the root may host a single red-red
  edge but every proper subtree is clean.  This is exactly {lit}`NoRedRed` after
  repainting the root black.
- The *doubly-black* deficit produced by removing a black node, which
  {lit}`baldL` / {lit}`baldR` absorb by rotating and recolouring.

Main results:

- Definitions {lit}`RBTree.rootColor`, {lit}`RBTree.NoRedRed2`.
- Balance invariant lemmas {lit}`RBTree.noRedRed_balanceLeft`,
  {lit}`RBTree.noRedRed_balanceRight`, {lit}`RBTree.balancedBlackHeight_balanceLeft`,
  {lit}`RBTree.balancedBlackHeight_balanceRight`.
- Definitions {lit}`RBTree.baldL`, {lit}`RBTree.baldR`, {lit}`RBTree.splitMin`,
  {lit}`RBTree.del`, {lit}`RBTree.delete`.
- Membership certificates {lit}`RBTree.inTree_baldL`, {lit}`RBTree.inTree_baldR`. -/

/-- The root colour of a tree; empty leaves count as black. -/
def rootColor : RBTree → Color
  | empty => Color.black
  | node c _ _ _ => c

/-- A weakened no-red-red invariant (`invc2`): the root may carry one red-red
edge, but every proper subtree already satisfies {name}`RBTree.NoRedRed`.  It is
defined as {name}`RBTree.NoRedRed` after repainting the root black. -/
def NoRedRed2 (t : RBTree) : Prop := NoRedRed (repaintRoot Color.black t)

/-- {name}`RBTree.NoRedRed2` on a node ignores the root colour constraint. -/
theorem noRedRed2_node_iff {c l k r} :
    NoRedRed2 (node c l k r) ↔ NoRedRed l ∧ NoRedRed r := by
  simp [NoRedRed2, repaintRoot, NoRedRed]

/-- Every {name}`RBTree.NoRedRed` tree is {name}`RBTree.NoRedRed2`. -/
theorem noRedRed2_of_noRedRed {t} (h : NoRedRed t) : NoRedRed2 t := noRedRed_repaint_black h

/-- A black-rooted {name}`RBTree.NoRedRed2` tree is fully {name}`RBTree.NoRedRed`. -/
theorem noRedRed_of_noRedRed2_rootBlack {t} (h2 : NoRedRed2 t) (hb : RootBlack t) :
    NoRedRed t := by
  cases t with
  | empty => trivial
  | node c l k r =>
      simp [RootBlack] at hb; subst hb
      rw [noRedRed2_node_iff] at h2; simp [NoRedRed]; exact ⟨h2.1, h2.2⟩

/-- Repainting the root red does not change {name}`RBTree.NoRedRed2`. -/
theorem noRedRed2_repaintRoot_red {t} : NoRedRed2 (repaintRoot Color.red t) ↔ NoRedRed2 t := by
  cases t <;> simp [NoRedRed2, repaintRoot, NoRedRed]

/-- Repainting a black root red drops the black height by one. -/
theorem blackHeight_repaintRoot_red_rootBlack {t} (h : RootBlack t) :
    blackHeight (repaintRoot Color.red t) = blackHeight t - 1 := by
  cases t with
  | empty => simp [repaintRoot, blackHeight]
  | node c l k r => simp [RootBlack] at h; subst h; simp [repaintRoot, blackHeight]

/-- Repainting the root red preserves balanced child black heights. -/
theorem balancedBlackHeight_repaintRoot_red {t} :
    BalancedBlackHeight (repaintRoot Color.red t) ↔ BalancedBlackHeight t := by
  cases t <;> simp [repaintRoot, BalancedBlackHeight]

/-! ### Balance invariant preservation

The insertion balancers {name}`RBTree.balanceLeft` / {name}`RBTree.balanceRight`
(CLRS `baliL` / `baliR`) not only preserve membership and black height (proved
above) but also repair a single red-red edge, taking one weakened
({name}`RBTree.NoRedRed2`) argument to a fully {name}`RBTree.NoRedRed` result. -/

/-- {name}`RBTree.balanceLeft` repairs a red-red edge in a weakened left child. -/
theorem noRedRed_balanceLeft {l y r} (hl : NoRedRed2 l) (hr : NoRedRed r) :
    NoRedRed (balanceLeft l y r) := by
  rw [NoRedRed2] at hl
  cases l with
  | empty => simpa [balanceLeft, NoRedRed, RootBlack] using hr
  | node lc ll lk lr =>
    cases lc with
    | black =>
        simp only [repaintRoot, NoRedRed, RootBlack] at hl
        simp only [balanceLeft, NoRedRed, RootBlack]; tauto
    | red =>
        simp only [repaintRoot, NoRedRed, RootBlack] at hl
        cases ll with
        | empty =>
            cases lr with
            | empty => simp [balanceLeft, NoRedRed, RootBlack]; tauto
            | node lrc lrl lrk lrr =>
                cases lrc <;> · simp only [balanceLeft, NoRedRed, RootBlack] at hl ⊢; tauto
        | node llc lll llk llr =>
            cases llc with
            | red => simp only [balanceLeft, NoRedRed, RootBlack] at hl ⊢; tauto
            | black =>
                cases lr with
                | empty => simp only [balanceLeft, NoRedRed, RootBlack] at hl ⊢; tauto
                | node lrc lrl lrk lrr =>
                    cases lrc <;> · simp only [balanceLeft, NoRedRed, RootBlack] at hl ⊢; tauto

/-- {name}`RBTree.balanceRight` repairs a red-red edge in a weakened right child. -/
theorem noRedRed_balanceRight {l y r} (hl : NoRedRed l) (hr : NoRedRed2 r) :
    NoRedRed (balanceRight l y r) := by
  rw [NoRedRed2] at hr
  cases r with
  | empty => simpa [balanceRight, NoRedRed, RootBlack] using hl
  | node rc rl rk rr =>
    cases rc with
    | black =>
        simp only [repaintRoot, NoRedRed, RootBlack] at hr
        simp only [balanceRight, NoRedRed, RootBlack]; tauto
    | red =>
        simp only [repaintRoot, NoRedRed, RootBlack] at hr
        cases rl with
        | empty =>
            cases rr with
            | empty => simp [balanceRight, NoRedRed, RootBlack]; tauto
            | node rrc rrl rrk rrr =>
                cases rrc <;> · simp only [balanceRight, NoRedRed, RootBlack] at hr ⊢; tauto
        | node rlc rll rlk rlr =>
            cases rlc with
            | red => simp only [balanceRight, NoRedRed, RootBlack] at hr ⊢; tauto
            | black =>
                cases rr with
                | empty => simp only [balanceRight, NoRedRed, RootBlack] at hr ⊢; tauto
                | node rrc rrl rrk rrr =>
                    cases rrc <;> · simp only [balanceRight, NoRedRed, RootBlack] at hr ⊢; tauto

/-- {name}`RBTree.balanceLeft` preserves balanced child black heights. -/
theorem balancedBlackHeight_balanceLeft {l y r}
    (hl : BalancedBlackHeight l) (hr : BalancedBlackHeight r)
    (hlr : blackHeight l = blackHeight r) :
    BalancedBlackHeight (balanceLeft l y r) := by
  unfold balanceLeft
  split <;> (simp_all [BalancedBlackHeight, blackHeight]; try omega)

/-- {name}`RBTree.balanceRight` preserves balanced child black heights. -/
theorem balancedBlackHeight_balanceRight {l y r}
    (hl : BalancedBlackHeight l) (hr : BalancedBlackHeight r)
    (hlr : blackHeight l = blackHeight r) :
    BalancedBlackHeight (balanceRight l y r) := by
  unfold balanceRight
  split <;> (simp_all [BalancedBlackHeight, blackHeight]; try omega)

/-! ### Deletion re-balancers `baldL` / `baldR`

After removing a black node from the left (respectively right) subtree, the
subtree carries a doubly-black deficit — its black height is one less than its
sibling.  {lit}`baldL` / {lit}`baldR` absorb the deficit,
possibly bubbling it one level up (the recoloured-red result). -/

/-- Deletion re-balancer for a black-deficient **left** child. -/
def baldL : RBTree → Nat → RBTree → RBTree
  | node Color.red a x b, k, r => node Color.red (node Color.black a x b) k r
  | l, k, node Color.black c y d => balanceRight l k (node Color.red c y d)
  | l, k, node Color.red (node Color.black c y d) z e =>
      node Color.red (node Color.black l k c) y (balanceRight d z (repaintRoot Color.red e))
  | l, k, r => node Color.red l k r

/-- Deletion re-balancer for a black-deficient **right** child. -/
def baldR : RBTree → Nat → RBTree → RBTree
  | l, k, node Color.red c y d => node Color.red l k (node Color.black c y d)
  | node Color.black a x b, k, r => balanceLeft (node Color.red a x b) k r
  | node Color.red a x (node Color.black c y d), k, r =>
      node Color.red (balanceLeft (repaintRoot Color.red a) x c) y (node Color.black d k r)
  | l, k, r => node Color.red l k r

/-- {name}`RBTree.baldL` preserves the key set (`{k} ∪ keys l ∪ keys r`). -/
theorem inTree_baldL (q : Nat) (l : RBTree) (k : Nat) (r : RBTree) :
    InTree q (baldL l k r) ↔ q = k ∨ InTree q l ∨ InTree q r := by
  unfold baldL
  split <;>
    simp [InTree, inTree_balanceRight_iff, inTree_repaintRoot_iff, or_assoc, or_left_comm]

/-- {name}`RBTree.baldR` preserves the key set (`{k} ∪ keys l ∪ keys r`). -/
theorem inTree_baldR (q : Nat) (l : RBTree) (k : Nat) (r : RBTree) :
    InTree q (baldR l k r) ↔ q = k ∨ InTree q l ∨ InTree q r := by
  unfold baldR
  split <;>
    simp [InTree, inTree_balanceLeft_iff, inTree_repaintRoot_iff, or_assoc, or_left_comm]

/-! ### Shape preservation for `baldL` / `baldR`

The re-balancers absorb a doubly-black deficit: the deficient child is
{name}`RBTree.NoRedRed2` and balanced with black height one less than its
sibling (or, degenerately, an empty child whose sibling has black height zero),
and the result is {name}`RBTree.NoRedRed2`, balanced, and has the sibling's
black height.  When the sibling's root is black the result is even fully
{name}`RBTree.NoRedRed`; this strengthening is needed when the parent node is
red. -/

/-- {name}`RBTree.balanceRight` against a reddened black sibling repairs a
deficient left child: fully {name}`RBTree.NoRedRed`, balanced, and black
height one more than the deficient child. -/
theorem balanceRight_red_right_shape {l : RBTree} {k z : Nat} {c d : RBTree}
    (hl : NoRedRed l) (hbl : BalancedBlackHeight l)
    (hnc : NoRedRed c) (hnd : NoRedRed d)
    (hbc : BalancedBlackHeight c) (hbd : BalancedBlackHeight d)
    (hcd : blackHeight c = blackHeight d) (heq : blackHeight l = blackHeight c) :
    NoRedRed (balanceRight l k (node Color.red c z d)) ∧
      BalancedBlackHeight (balanceRight l k (node Color.red c z d)) ∧
      blackHeight (balanceRight l k (node Color.red c z d)) = blackHeight l + 1 := by
  have hn2 : NoRedRed2 (node Color.red c z d) := noRedRed2_node_iff.mpr ⟨hnc, hnd⟩
  have hbalR : BalancedBlackHeight (node Color.red c z d) := ⟨hbc, hbd, hcd⟩
  exact ⟨noRedRed_balanceRight hl hn2,
    balancedBlackHeight_balanceRight hbl hbalR heq,
    by rw [blackHeight_balanceRight]; simp [blackHeight]⟩

/-- The third {name}`RBTree.baldL` case (red sibling with a black left child)
repairs the deficit while bubbling a red root up. -/
theorem baldL_red_sibling_shape {l : RBTree} {k w z : Nat} {a b e : RBTree}
    (hl : NoRedRed l) (hbl : BalancedBlackHeight l)
    (hna : NoRedRed a) (hnb : NoRedRed b) (hne : NoRedRed e)
    (hba : BalancedBlackHeight a) (hbb : BalancedBlackHeight b)
    (hbe : BalancedBlackHeight e)
    (hab : blackHeight a = blackHeight b)
    (hbeq : blackHeight a + 1 = blackHeight e)
    (hle : blackHeight l = blackHeight a)
    (hre : RootBlack e) :
    NoRedRed2 (node Color.red (node Color.black l k a) w
        (balanceRight b z (repaintRoot Color.red e))) ∧
      BalancedBlackHeight (node Color.red (node Color.black l k a) w
        (balanceRight b z (repaintRoot Color.red e))) ∧
      blackHeight (node Color.red (node Color.black l k a) w
        (balanceRight b z (repaintRoot Color.red e))) = blackHeight l + 1 := by
  have hnlka : NoRedRed (node Color.black l k a) := by
    simp [NoRedRed]; exact ⟨hl, hna⟩
  have hblka : BalancedBlackHeight (node Color.black l k a) := ⟨hbl, hba, hle⟩
  have hn2e : NoRedRed2 (repaintRoot Color.red e) :=
    noRedRed2_repaintRoot_red.mpr (noRedRed2_of_noRedRed hne)
  have hnbz : NoRedRed (balanceRight b z (repaintRoot Color.red e)) :=
    noRedRed_balanceRight hnb hn2e
  have hbe2 : blackHeight (repaintRoot Color.red e) = blackHeight a := by
    rw [blackHeight_repaintRoot_red_rootBlack hre]; omega
  have hbbz : BalancedBlackHeight (balanceRight b z (repaintRoot Color.red e)) :=
    balancedBlackHeight_balanceRight hbb (balancedBlackHeight_repaintRoot Color.red hbe)
      (hbe2.trans hab).symm
  have hbhz : blackHeight (balanceRight b z (repaintRoot Color.red e)) =
      blackHeight b + 1 := by
    rw [blackHeight_balanceRight]; simp [blackHeight]
  refine ⟨noRedRed2_node_iff.mpr ⟨hnlka, hnbz⟩, ⟨hblka, hbbz, ?_⟩, ?_⟩
  · simp [blackHeight]; omega
  · simp [blackHeight]

/-- {name}`RBTree.baldL` absorbs a doubly-black deficit in the left child: the
result is weakened red-red free and balanced, has the right sibling's black
height, and is fully {name}`RBTree.NoRedRed` when the right sibling's root is
black. -/
theorem baldL_shape {l : RBTree} {k : Nat} {r : RBTree}
    (hl2 : NoRedRed2 l) (hbl : BalancedBlackHeight l)
    (hr : NoRedRed r) (hbr : BalancedBlackHeight r)
    (hdef : blackHeight l + 1 = blackHeight r ∨ (l = empty ∧ blackHeight r = 0)) :
    NoRedRed2 (baldL l k r) ∧ BalancedBlackHeight (baldL l k r) ∧
      blackHeight (baldL l k r) = blackHeight r ∧
      (RootBlack r → NoRedRed (baldL l k r)) := by
  -- The red-left-child case is independent of the shape of `r`.
  have case1 : ∀ a b : RBTree, ∀ x : Nat,
      NoRedRed2 (node Color.red a x b) → BalancedBlackHeight (node Color.red a x b) →
      blackHeight (node Color.red a x b) + 1 = blackHeight r →
      NoRedRed2 (baldL (node Color.red a x b) k r) ∧
        BalancedBlackHeight (baldL (node Color.red a x b) k r) ∧
        blackHeight (baldL (node Color.red a x b) k r) = blackHeight r ∧
        (RootBlack r → NoRedRed (baldL (node Color.red a x b) k r)) := by
    intro a b x hl2' hbl' hd
    have hred : baldL (node Color.red a x b) k r =
        node Color.red (node Color.black a x b) k r := rfl
    have hlb : NoRedRed (node Color.black a x b) := hl2'
    have hbb : BalancedBlackHeight (node Color.black a x b) := hbl'
    rw [hred]
    have hbh : blackHeight (node Color.black a x b) = blackHeight r := by
      simp [blackHeight] at hd ⊢; omega
    exact ⟨noRedRed2_node_iff.mpr ⟨hlb, hr⟩, ⟨hbb, hbr, hbh⟩, hbh,
      fun hrb => ⟨hlb, hr, fun _ => ⟨rfl, hrb⟩⟩⟩
  cases l with
  | empty =>
      cases r with
      | empty =>
          simp [baldL, NoRedRed2, repaintRoot, NoRedRed, BalancedBlackHeight, blackHeight,
            RootBlack]
      | node rc rl z rr =>
          cases rc with
          | black =>
              obtain ⟨hnc, hnd, -⟩ := hr
              obtain ⟨hbc, hbd, hcd⟩ := hbr
              have hrl0 : blackHeight rl = 0 := by
                rcases hdef with hd | ⟨-, hd⟩ <;> simp [blackHeight] at hd; omega
              have hred : baldL empty k (node Color.black rl z rr) =
                  balanceRight empty k (node Color.red rl z rr) := by simp [baldL]
              rw [hred]
              obtain ⟨hn, hbal, hbh⟩ := balanceRight_red_right_shape (l := empty) trivial
                trivial hnc hnd hbc hbd hcd (by simp [blackHeight, hrl0])
              refine ⟨noRedRed2_of_noRedRed hn, hbal, ?_, fun _ => hn⟩
              rw [hbh]; simp [blackHeight, hrl0]
          | red =>
              cases rl with
              | empty =>
                  have hred : baldL empty k (node Color.red empty z rr) =
                      node Color.red empty k (node Color.red empty z rr) := by simp [baldL]
                  rw [hred]
                  refine ⟨noRedRed2_node_iff.mpr ⟨trivial, hr⟩, ⟨trivial, hbr, ?_⟩, ?_,
                    fun hrb => by simp [RootBlack] at hrb⟩
                  · simp [blackHeight]
                  · simp [blackHeight]
              | node rlc rll rlk rlr =>
                  cases rlc with
                  | red =>
                      exfalso
                      exact absurd (hr.2.2 rfl).1 (by simp [RootBlack])
                  | black =>
                      obtain ⟨hnAB, hne, hroots⟩ := hr
                      obtain ⟨hna, hnb, -⟩ := hnAB
                      obtain ⟨hbAB, hbe, hbhAB⟩ := hbr
                      obtain ⟨hba, hbb, hab⟩ := hbAB
                      have hrll0 : blackHeight rll = 0 := by
                        rcases hdef with hd | ⟨-, hd⟩ <;> simp [blackHeight] at hd; omega
                      have hred : baldL empty k
                            (node Color.red (node Color.black rll rlk rlr) z rr) =
                          node Color.red (node Color.black empty k rll) rlk
                            (balanceRight rlr z (repaintRoot Color.red rr)) := by simp [baldL]
                      rw [hred]
                      obtain ⟨hn2o, hbalo, hbho⟩ := baldL_red_sibling_shape (l := empty)
                        trivial trivial hna hnb hne hba hbb hbe hab
                        (by simpa [blackHeight] using hbhAB)
                        (by simp [blackHeight, hrll0]) (hroots rfl).2
                      refine ⟨hn2o, hbalo, ?_, fun hrb => by simp [RootBlack] at hrb⟩
                      rw [hbho]; simp [blackHeight, hrll0]
  | node lc la lx lb =>
      cases lc with
      | red =>
          rcases hdef with hd | ⟨hl', -⟩
          · exact case1 la lb lx hl2 hbl hd
          · exact absurd hl' (by simp)
      | black =>
          cases r with
          | empty =>
              exfalso
              rcases hdef with hd | ⟨hl', -⟩
              · simp [blackHeight] at hd
              · exact absurd hl' (by simp)
          | node rc rl z rr =>
              cases rc with
              | black =>
                  obtain ⟨hnc, hnd, -⟩ := hr
                  obtain ⟨hbc, hbd, hcd⟩ := hbr
                  have hnl : NoRedRed (node Color.black la lx lb) :=
                    noRedRed_of_noRedRed2_rootBlack hl2 rfl
                  have heq : blackHeight (node Color.black la lx lb) = blackHeight rl := by
                    rcases hdef with hd | ⟨hl', -⟩
                    · simp [blackHeight] at hd ⊢; omega
                    · exact absurd hl' (by simp)
                  have hred : baldL (node Color.black la lx lb) k (node Color.black rl z rr) =
                      balanceRight (node Color.black la lx lb) k
                        (node Color.red rl z rr) := rfl
                  rw [hred]
                  obtain ⟨hn, hbal, hbh⟩ := balanceRight_red_right_shape hnl hbl hnc hnd
                    hbc hbd hcd heq
                  refine ⟨noRedRed2_of_noRedRed hn, hbal, ?_, fun _ => hn⟩
                  rw [hbh]; simp [blackHeight] at heq ⊢; omega
              | red =>
                  cases rl with
                  | empty =>
                      exfalso
                      rcases hdef with hd | ⟨hl', -⟩
                      · simp [blackHeight] at hd
                      · exact absurd hl' (by simp)
                  | node rlc rll rlk rlr =>
                      cases rlc with
                      | red =>
                          exfalso
                          exact absurd (hr.2.2 rfl).1 (by simp [RootBlack])
                      | black =>
                          obtain ⟨hnAB, hne, hroots⟩ := hr
                          obtain ⟨hna, hnb, -⟩ := hnAB
                          obtain ⟨hbAB, hbe, hbhAB⟩ := hbr
                          obtain ⟨hba, hbb, hab⟩ := hbAB
                          have hnl : NoRedRed (node Color.black la lx lb) :=
                            noRedRed_of_noRedRed2_rootBlack hl2 rfl
                          have hle : blackHeight (node Color.black la lx lb) =
                              blackHeight rll := by
                            rcases hdef with hd | ⟨hl', -⟩
                            · simp [blackHeight] at hd ⊢; omega
                            · exact absurd hl' (by simp)
                          have hred : baldL (node Color.black la lx lb) k
                                (node Color.red (node Color.black rll rlk rlr) z rr) =
                              node Color.red
                                (node Color.black (node Color.black la lx lb) k rll) rlk
                                (balanceRight rlr z (repaintRoot Color.red rr)) := rfl
                          rw [hred]
                          obtain ⟨hn2o, hbalo, hbho⟩ := baldL_red_sibling_shape hnl hbl
                            hna hnb hne hba hbb hbe hab (by simpa [blackHeight] using hbhAB)
                            hle (hroots rfl).2
                          refine ⟨hn2o, hbalo, ?_, fun hrb => by simp [RootBlack] at hrb⟩
                          rw [hbho]; simp [blackHeight] at hle ⊢; omega

/-- {name}`RBTree.balanceLeft` against a reddened black sibling repairs a
deficient right child: fully {name}`RBTree.NoRedRed`, balanced, and black
height one more than the deficient child. -/
theorem balanceLeft_red_left_shape {a b r : RBTree} {x k : Nat}
    (hna : NoRedRed a) (hnb : NoRedRed b) (hnr : NoRedRed r)
    (hba : BalancedBlackHeight a) (hbb : BalancedBlackHeight b)
    (hbr : BalancedBlackHeight r)
    (hab : blackHeight a = blackHeight b) (heq : blackHeight r = blackHeight a) :
    NoRedRed (balanceLeft (node Color.red a x b) k r) ∧
      BalancedBlackHeight (balanceLeft (node Color.red a x b) k r) ∧
      blackHeight (balanceLeft (node Color.red a x b) k r) = blackHeight a + 1 := by
  have hn2 : NoRedRed2 (node Color.red a x b) := noRedRed2_node_iff.mpr ⟨hna, hnb⟩
  have hbalL : BalancedBlackHeight (node Color.red a x b) := ⟨hba, hbb, hab⟩
  refine ⟨noRedRed_balanceLeft hn2 hnr,
    balancedBlackHeight_balanceLeft hbalL hbr ?_,
    by rw [blackHeight_balanceLeft]; simp [blackHeight]⟩
  simp [blackHeight]; exact heq.symm

/-- The third {name}`RBTree.baldR` case (red sibling with a black right child)
repairs the deficit while bubbling a red root up. -/
theorem baldR_red_sibling_shape {a c d r : RBTree} {x y k : Nat}
    (hna : NoRedRed a) (hnc : NoRedRed c) (hnd : NoRedRed d) (hnr : NoRedRed r)
    (hba : BalancedBlackHeight a) (hbc : BalancedBlackHeight c)
    (hbd : BalancedBlackHeight d) (hbr : BalancedBlackHeight r)
    (hab : blackHeight a = blackHeight c + 1)
    (hcd : blackHeight c = blackHeight d)
    (heq : blackHeight r = blackHeight c)
    (hra : RootBlack a) :
    NoRedRed2 (node Color.red (balanceLeft (repaintRoot Color.red a) x c) y
        (node Color.black d k r)) ∧
      BalancedBlackHeight (node Color.red (balanceLeft (repaintRoot Color.red a) x c) y
        (node Color.black d k r)) ∧
      blackHeight (node Color.red (balanceLeft (repaintRoot Color.red a) x c) y
        (node Color.black d k r)) = blackHeight a := by
  have hn2a : NoRedRed2 (repaintRoot Color.red a) :=
    noRedRed2_repaintRoot_red.mpr (noRedRed2_of_noRedRed hna)
  have hnbl : NoRedRed (balanceLeft (repaintRoot Color.red a) x c) :=
    noRedRed_balanceLeft hn2a hnc
  have hndkr : NoRedRed (node Color.black d k r) := by
    simp [NoRedRed]; exact ⟨hnd, hnr⟩
  have hba2 : blackHeight (repaintRoot Color.red a) = blackHeight c := by
    rw [blackHeight_repaintRoot_red_rootBlack hra]; omega
  have hbbl : BalancedBlackHeight (balanceLeft (repaintRoot Color.red a) x c) :=
    balancedBlackHeight_balanceLeft (balancedBlackHeight_repaintRoot Color.red hba) hbc hba2
  have hbhbl : blackHeight (balanceLeft (repaintRoot Color.red a) x c) =
      blackHeight a := by
    rw [blackHeight_balanceLeft]; simp [blackHeight]; rw [hba2]; omega
  have hbd2 : BalancedBlackHeight (node Color.black d k r) := ⟨hbd, hbr, by omega⟩
  refine ⟨noRedRed2_node_iff.mpr ⟨hnbl, hndkr⟩, ⟨hbbl, hbd2, ?_⟩, ?_⟩
  · rw [hbhbl]; simp [blackHeight]; omega
  · simpa [blackHeight] using hbhbl

/-- {name}`RBTree.baldR` absorbs a doubly-black deficit in the right child:
the result is weakened red-red free and balanced, has the left sibling's black
height, and is fully {name}`RBTree.NoRedRed` when the left sibling's root is
black. -/
theorem baldR_shape {l : RBTree} {k : Nat} {r : RBTree}
    (hr2 : NoRedRed2 r) (hbr : BalancedBlackHeight r)
    (hl : NoRedRed l) (hbl : BalancedBlackHeight l)
    (hdef : blackHeight r + 1 = blackHeight l ∨ (r = empty ∧ blackHeight l = 0)) :
    NoRedRed2 (baldR l k r) ∧ BalancedBlackHeight (baldR l k r) ∧
      blackHeight (baldR l k r) = blackHeight l ∧
      (RootBlack l → NoRedRed (baldR l k r)) := by
  -- The red-right-child case is independent of the shape of `l`.
  have case1 : ∀ c d : RBTree, ∀ y : Nat,
      NoRedRed2 (node Color.red c y d) → BalancedBlackHeight (node Color.red c y d) →
      blackHeight (node Color.red c y d) + 1 = blackHeight l →
      NoRedRed2 (baldR l k (node Color.red c y d)) ∧
        BalancedBlackHeight (baldR l k (node Color.red c y d)) ∧
        blackHeight (baldR l k (node Color.red c y d)) = blackHeight l ∧
        (RootBlack l → NoRedRed (baldR l k (node Color.red c y d))) := by
    intro c d y hr2' hbr' hd
    have hred : baldR l k (node Color.red c y d) =
        node Color.red l k (node Color.black c y d) := rfl
    have hcd' : NoRedRed (node Color.black c y d) := hr2'
    have hbc' : BalancedBlackHeight (node Color.black c y d) := hbr'
    rw [hred]
    have hbh : blackHeight (node Color.black c y d) = blackHeight l := by
      simp [blackHeight] at hd ⊢; omega
    exact ⟨noRedRed2_node_iff.mpr ⟨hl, hcd'⟩, ⟨hbl, hbc', hbh.symm⟩,
      by simp [blackHeight], fun hlb => ⟨hl, hcd', fun _ => ⟨hlb, rfl⟩⟩⟩
  cases r with
  | empty =>
      cases l with
      | empty =>
          simp [baldR, NoRedRed2, repaintRoot, NoRedRed, BalancedBlackHeight, blackHeight,
            RootBlack]
      | node lc la lx lb =>
          cases lc with
          | black =>
              obtain ⟨hna, hnb, -⟩ := hl
              obtain ⟨hba, hbb, hab⟩ := hbl
              have heq : blackHeight empty = blackHeight la := by
                rcases hdef with hd | ⟨-, hd⟩ <;> simp [blackHeight] at hd ⊢; omega
              have hred : baldR (node Color.black la lx lb) k empty =
                  balanceLeft (node Color.red la lx lb) k empty := rfl
              rw [hred]
              obtain ⟨hn, hbal, hbh⟩ := balanceLeft_red_left_shape (r := empty) hna hnb
                trivial hba hbb trivial hab heq
              refine ⟨noRedRed2_of_noRedRed hn, hbal, ?_, fun _ => hn⟩
              rw [hbh]; simp [blackHeight]
          | red =>
              cases lb with
              | empty =>
                  have hred : baldR (node Color.red la lx empty) k empty =
                      node Color.red (node Color.red la lx empty) k empty := rfl
                  rw [hred]
                  have habh : blackHeight la = 0 := by
                    have h2 := hbl.2.2; simpa [blackHeight] using h2
                  refine ⟨noRedRed2_node_iff.mpr ⟨hl, trivial⟩, ⟨hbl, trivial, ?_⟩, ?_,
                    fun hrb => by simp [RootBlack] at hrb⟩
                  · simp [blackHeight, habh]
                  · simp [blackHeight]
              | node lbc c y d =>
                  cases lbc with
                  | red =>
                      exfalso
                      exact absurd (hl.2.2 rfl).2 (by simp [RootBlack])
                  | black =>
                      obtain ⟨hna, hnBB, hroots⟩ := hl
                      obtain ⟨hnc, hnd, -⟩ := hnBB
                      obtain ⟨hba, hbBB, habB⟩ := hbl
                      obtain ⟨hbc, hbd, hcd⟩ := hbBB
                      have heq : blackHeight empty = blackHeight c := by
                        rcases hdef with hd | ⟨-, hd⟩ <;>
                          simp [blackHeight] at hd habB ⊢ <;> omega
                      have hred : baldR (node Color.red la lx (node Color.black c y d)) k
                            empty =
                          node Color.red (balanceLeft (repaintRoot Color.red la) lx c) y
                            (node Color.black d k empty) := rfl
                      rw [hred]
                      obtain ⟨hn2o, hbalo, hbho⟩ := baldR_red_sibling_shape (r := empty)
                        hna hnc hnd trivial hba hbc hbd trivial
                        (by simpa [blackHeight] using habB)
                        hcd heq (hroots rfl).1
                      refine ⟨hn2o, hbalo, ?_, fun hrb => by simp [RootBlack] at hrb⟩
                      rw [hbho]; simp [blackHeight]
  | node rc rl z rr =>
      cases rc with
      | red =>
          rcases hdef with hd | ⟨hre, -⟩
          · exact case1 rl rr z hr2 hbr hd
          · exact absurd hre (by simp)
      | black =>
          cases l with
          | empty =>
              exfalso
              rcases hdef with hd | ⟨hre, -⟩
              · simp [blackHeight] at hd
              · exact absurd hre (by simp)
          | node lc la lx lb =>
              cases lc with
              | black =>
                  obtain ⟨hna, hnb, -⟩ := hl
                  obtain ⟨hba, hbb, hab⟩ := hbl
                  have hnr : NoRedRed (node Color.black rl z rr) :=
                    noRedRed_of_noRedRed2_rootBlack hr2 rfl
                  have heq : blackHeight (node Color.black rl z rr) = blackHeight la := by
                    rcases hdef with hd | ⟨hre, -⟩
                    · simp [blackHeight] at hd ⊢; omega
                    · exact absurd hre (by simp)
                  have hred : baldR (node Color.black la lx lb) k
                        (node Color.black rl z rr) =
                      balanceLeft (node Color.red la lx lb) k
                        (node Color.black rl z rr) := rfl
                  rw [hred]
                  obtain ⟨hn, hbal, hbh⟩ := balanceLeft_red_left_shape hna hnb hnr
                    hba hbb hbr hab heq
                  refine ⟨noRedRed2_of_noRedRed hn, hbal, ?_, fun _ => hn⟩
                  rw [hbh]; simp [blackHeight]
              | red =>
                  cases lb with
                  | empty =>
                      exfalso
                      rcases hdef with hd | ⟨hre, -⟩
                      · obtain ⟨-, -, habh⟩ := hbl
                        simp [blackHeight] at hd habh; omega
                      · exact absurd hre (by simp)
                  | node lbc c y d =>
                      cases lbc with
                      | red =>
                          exfalso
                          exact absurd (hl.2.2 rfl).2 (by simp [RootBlack])
                      | black =>
                          obtain ⟨hna, hnBB, hroots⟩ := hl
                          obtain ⟨hnc, hnd, -⟩ := hnBB
                          obtain ⟨hba, hbBB, habB⟩ := hbl
                          obtain ⟨hbc, hbd, hcd⟩ := hbBB
                          have hnr : NoRedRed (node Color.black rl z rr) :=
                            noRedRed_of_noRedRed2_rootBlack hr2 rfl
                          have heq : blackHeight (node Color.black rl z rr) =
                              blackHeight c := by
                            rcases hdef with hd | ⟨hre, -⟩
                            · simp [blackHeight] at hd habB ⊢; omega
                            · exact absurd hre (by simp)
                          have hred : baldR (node Color.red la lx (node Color.black c y d)) k
                                (node Color.black rl z rr) =
                              node Color.red (balanceLeft (repaintRoot Color.red la) lx c) y
                                (node Color.black d k (node Color.black rl z rr)) := rfl
                          rw [hred]
                          obtain ⟨hn2o, hbalo, hbho⟩ := baldR_red_sibling_shape hna hnc hnd
                            hnr hba hbc hbd hbr (by simpa [blackHeight] using habB)
                            hcd heq (hroots rfl).1
                          refine ⟨hn2o, hbalo, ?_, fun hrb => by simp [RootBlack] at hrb⟩
                          rw [hbho]; simp [blackHeight]

/-! ### Binary-search-tree ordering predicate

The BST property (all keys in the left subtree are less than the root, all keys
in the right subtree are greater) is needed for the \"key not present after delete\"
direction of the membership theorem.  Every red-black tree is a BST, so this is
a valid assumption for all inputs. -/

/-- A binary-search-tree ordering predicate: all keys in the left subtree are less
than the node's key, all keys in the right subtree are greater. -/
def BST : RBTree → Prop
  | empty => True
  | node _ l k r => BST l ∧ BST r ∧ (∀ x, InTree x l → x < k) ∧ (∀ x, InTree x r → k < x)

/-- Extract the BST property from a node. -/
theorem bst_node {c l k r} (h : BST (node c l k r)) : BST l ∧ BST r := by
  simp [BST] at h; exact ⟨h.1, h.2.1⟩

/-! ### Minimum deletion and tree merging -/

/-- Find and remove the minimum key from a non-empty tree.
Returns `(min_key, tree_without_min)`.  On the way back up the left spine the
removed black node leaves a doubly-black deficit, which is absorbed by
{name}`RBTree.baldL` exactly as in the recursive deletion {lit}`del`. -/
def splitMin : RBTree → Nat × RBTree
  | empty => (0, empty)  -- unreachable on valid inputs
  | node _ empty k r => (k, r)
  | node _ l k r =>
      let (m, l') := splitMin l
      if rootBlack l then (m, baldL l' k r)
      else (m, node Color.red l' k r)

/-- The minimum key removed by {name}`splitMin` is indeed in the original tree. -/
theorem inTree_splitMin_mem {t : RBTree} (h : t ≠ empty) : InTree (splitMin t).1 t := by
  induction t with
  | empty => exact (h rfl).elim
  | node c l k r ihl =>
    cases l with
    | empty => simp [splitMin, InTree]
    | node lc ll lk lr =>
        have hne : node lc ll lk lr ≠ empty := by
          intro h'; injection h'
        have ih := ihl hne
        by_cases hrb : rootBlack (node lc ll lk lr) = true <;>
          simpa [splitMin, hrb, InTree] using Or.inr (Or.inl ih)

/-- If a key is in the result of {name}`splitMin`, it was in the original tree
(splitMin never introduces keys). -/
theorem inTree_splitMin_forward {t : RBTree} (h : t ≠ empty) (q : Nat) :
    InTree q (splitMin t).2 → InTree q t := by
  induction t with
  | empty => exact (h rfl).elim
  | node c l k r ihl =>
    cases l with
    | empty =>
        simp [splitMin, InTree]
        intro hqr; exact Or.inr hqr
    | node lc ll lk lr =>
        have hne : node lc ll lk lr ≠ empty := by
          intro h'; injection h'
        have ih := ihl hne
        by_cases hrb : rootBlack (node lc ll lk lr) = true <;>
          · simp [splitMin, hrb, InTree, inTree_baldL]
            intro h
            rcases h with (hqk | hql' | hqr)
            · exact Or.inl hqk
            · have hql := ih hql'
              exact Or.inr (Or.inl hql)
            · exact Or.inr (Or.inr hqr)

/-- If a key `q` is in the original tree and is not the removed minimum, then it is
still in the tree after {name}`splitMin`. -/
theorem inTree_splitMin_iff {t : RBTree} (h : t ≠ empty) (q : Nat) :
    (InTree q t ∧ q ≠ (splitMin t).1) → InTree q (splitMin t).2 := by
  induction t with
  | empty => exact (h rfl).elim
  | node c l k r ihl =>
    cases l with
    | empty =>
        simp [splitMin, InTree]
        intro hq hqne
        rcases hq with (hqk | hqr)
        · exfalso; exact hqne hqk
        · exact hqr
    | node lc ll lk lr =>
        have hne : node lc ll lk lr ≠ empty := by
          intro h'; injection h'
        have ih := ihl hne
        by_cases hrb : rootBlack (node lc ll lk lr) = true <;>
          · simp [splitMin, hrb, InTree, inTree_baldL]
            intro hq hqne
            rcases hq with (hqk | hql | hqr)
            · exact Or.inl hqk
            · have hql' : InTree q (node lc ll lk lr) := by
                simpa [InTree] using hql
              have ih' := ih ⟨hql', hqne⟩
              exact Or.inr (Or.inl ih')
            · exact Or.inr (Or.inr hqr)

/-- {name}`splitMin` preserves the red-black shape invariant: the remaining
tree is weakened red-red free and balanced, loses exactly one black height
when the input root is black, and keeps both its black height and the full
{name}`RBTree.NoRedRed` invariant when the input root is red. -/
theorem splitMin_invariant {t : RBTree} (h : RedRootedRB t) (hne : t ≠ empty) :
    NoRedRed2 (splitMin t).2 ∧ BalancedBlackHeight (splitMin t).2 ∧
      (RootBlack t → blackHeight (splitMin t).2 + 1 = blackHeight t) ∧
      (¬ RootBlack t → blackHeight (splitMin t).2 = blackHeight t ∧
        NoRedRed (splitMin t).2) := by
  induction t with
  | empty => exact (hne rfl).elim
  | node c l k r ihl =>
      have hNoRed := h.1
      have hBal := h.2
      rcases hBal with ⟨hBalL, hBalR, hEqHeight⟩
      have hRootedL : RedRootedRB l := ⟨hNoRed.1, hBalL⟩
      have hRootedR : RedRootedRB r := ⟨hNoRed.2.1, hBalR⟩
      cases l with
      | empty =>
          have hsp : (splitMin (node c empty k r)).2 = r := by simp [splitMin]
          rw [hsp]
          have hbh0 : blackHeight r = 0 := by
            have h2 := hEqHeight.symm; simpa [blackHeight] using h2
          refine ⟨noRedRed2_of_noRedRed hNoRed.2.1, hBalR, ?_, ?_⟩
          · intro hroot
            subst hroot; simp [blackHeight, hbh0]
          · intro hnroot
            have hc : c = Color.red := by
              cases c with
              | black => exact absurd rfl hnroot
              | red => rfl
            subst hc
            exact ⟨by simp [blackHeight, hbh0], hNoRed.2.1⟩
      | node lc ll lk lr =>
          have hneL : node lc ll lk lr ≠ empty := by
            intro h'; injection h'
          have ih := ihl hRootedL hneL
          by_cases hlb : rootBlack (node lc ll lk lr) = true
          · have hsp : (splitMin (node c (node lc ll lk lr) k r)).2 =
                baldL (splitMin (node lc ll lk lr)).2 k r := by simp [splitMin, hlb]
            rw [hsp]
            have hRb : RootBlack (node lc ll lk lr) := (rootBlack_eq_RootBlack _).mp hlb
            have hdef : blackHeight (splitMin (node lc ll lk lr)).2 + 1 = blackHeight r ∨
                ((splitMin (node lc ll lk lr)).2 = empty ∧ blackHeight r = 0) :=
              Or.inl (by have h2 := ih.2.2.1 hRb; omega)
            obtain ⟨hn2, hbal2, hbh2, hfull⟩ := baldL_shape ih.1 ih.2.1 hNoRed.2.1 hBalR hdef
            refine ⟨hn2, hbal2, ?_, ?_⟩
            · intro hroot
              subst hroot; simp [blackHeight] at hEqHeight ⊢; omega
            · intro hnroot
              have hc : c = Color.red := by
                cases c with
                | black => exact absurd rfl hnroot
                | red => rfl
              have hRootR := (hNoRed.2.2 hc).2
              subst hc
              exact ⟨by simp [blackHeight] at hEqHeight ⊢; omega, hfull hRootR⟩
          · have hsp : (splitMin (node c (node lc ll lk lr) k r)).2 =
                node Color.red (splitMin (node lc ll lk lr)).2 k r := by
              simp [splitMin, hlb]
            rw [hsp]
            have hRnb : ¬ RootBlack (node lc ll lk lr) :=
              fun hr' => hlb ((rootBlack_eq_RootBlack _).mpr hr')
            obtain ⟨hbhL, hnL⟩ := ih.2.2.2 hRnb
            have hc : c = Color.black := by
              cases c with
              | black => rfl
              | red => exact absurd (hNoRed.2.2 rfl).1 hRnb
            subst hc
            refine ⟨noRedRed2_node_iff.mpr ⟨hnL, hNoRed.2.1⟩,
              ⟨ih.2.1, hBalR, by omega⟩, ?_, ?_⟩
            · intro _; simp [blackHeight] at hbhL ⊢; omega
            · intro hnb; exact (hnb rfl).elim

/-- Merge two trees into one, used when deleting a node with two children.
All keys in `l` must be less than all keys in `r`.  When `r` is black-rooted,
removing its minimum leaves a deficit that {name}`RBTree.baldR` absorbs; when
`r` is red-rooted no deficit arises and a plain red node is rebuilt. -/
def join (l r : RBTree) : RBTree :=
  if h : r = empty then l
  else if h' : l = empty then r
  else
    let (m, r') := splitMin r
    if rootBlack r then baldR l m r'
    else node Color.red l m r'

/-- {name}`join` preserves the union of key sets. -/
theorem inTree_join_iff (q : Nat) (l r : RBTree) :
    InTree q (join l r) ↔ InTree q l ∨ InTree q r := by
  unfold join
  split_ifs with hr hl hrb
  · subst hr; simp [InTree]
  · subst hl; simp [InTree]
  · simp [inTree_baldR]
    constructor
    · intro h
      rcases h with (hqm | hql | hqr)
      · have hmr : InTree (splitMin r).1 r := inTree_splitMin_mem hr
        subst hqm; exact Or.inr hmr
      · exact Or.inl hql
      · have hqrT : InTree q r := inTree_splitMin_forward hr q hqr
        exact Or.inr hqrT
    · intro h
      rcases h with (hql | hqr)
      · exact Or.inr (Or.inl hql)
      · by_cases hqe : q = (splitMin r).1
        · subst q; exact Or.inl rfl
        · have hqr' : InTree q (splitMin r).2 :=
            inTree_splitMin_iff hr q ⟨hqr, hqe⟩
          exact Or.inr (Or.inr hqr')
  · simp [InTree]
    constructor
    · intro h
      rcases h with (hqm | hql | hqr)
      · have hmr : InTree (splitMin r).1 r := inTree_splitMin_mem hr
        subst hqm; exact Or.inr hmr
      · exact Or.inl hql
      · have hqrT : InTree q r := inTree_splitMin_forward hr q hqr
        exact Or.inr hqrT
    · intro h
      rcases h with (hql | hqr)
      · exact Or.inr (Or.inl hql)
      · by_cases hqe : q = (splitMin r).1
        · subst q; exact Or.inl rfl
        · have hqr' : InTree q (splitMin r).2 :=
            inTree_splitMin_iff hr q ⟨hqr, hqe⟩
          exact Or.inr (Or.inr hqr')

/-! ### Executable deletion -/

/-- Recursive deletion from a red-black tree.
Returns a tree that is {name}`NoRedRed2` when the input is {name}`RedBlackShape`
shaped, and has black height either the same as the input or one less. -/
def del (x : Nat) : RBTree → RBTree
  | empty => empty
  | node c l y r =>
    if x < y then
      if rootBlack l then baldL (del x l) y r
      else node Color.red (del x l) y r
    else if x > y then
      if rootBlack r then baldR l y (del x r)
      else node Color.red l y (del x r)
    else join l r

/-- Delete a key from a red-black tree while preserving the global red-black shape. -/
def delete (x : Nat) (t : RBTree) : RBTree :=
  repaintRoot Color.black (del x t)

/-- Recursive deletion preserves the red-black shape invariant, mirroring
{name}`RBTree.insertFixup_invariant`: the result is weakened red-red free and
balanced; a black-rooted input loses exactly one black height, while a
red-rooted input keeps its black height and satisfies the full
{name}`RBTree.NoRedRed` invariant. -/
theorem del_invariant {x : Nat} {t : RBTree} (h : RedRootedRB t) :
    NoRedRed2 (del x t) ∧ BalancedBlackHeight (del x t) ∧
      (RootBlack t → t ≠ empty → blackHeight (del x t) + 1 = blackHeight t) ∧
      (¬ RootBlack t → blackHeight (del x t) = blackHeight t ∧ NoRedRed (del x t)) := by
  induction t with
  | empty =>
      refine ⟨by simp [del, NoRedRed2, repaintRoot, NoRedRed],
        by simp [del, BalancedBlackHeight], ?_, ?_⟩
      · intro _ hne; exact (hne rfl).elim
      · intro hnb; exact absurd True.intro hnb
  | node c l y r ihl ihr =>
      have hNoRed := h.1
      have hBal := h.2
      rcases hBal with ⟨hBalL, hBalR, hEqHeight⟩
      have hRootedL : RedRootedRB l := ⟨hNoRed.1, hBalL⟩
      have hRootedR : RedRootedRB r := ⟨hNoRed.2.1, hBalR⟩
      have ihL := ihl hRootedL
      have ihR := ihr hRootedR
      by_cases h1 : x < y
      · by_cases hlb : rootBlack l = true
        · have hdel : del x (node c l y r) = baldL (del x l) y r := by simp [del, h1, hlb]
          rw [hdel]
          have hdef : blackHeight (del x l) + 1 = blackHeight r ∨
              (del x l = empty ∧ blackHeight r = 0) := by
            cases l with
            | empty =>
                right
                exact ⟨by simp [del], by simpa [blackHeight] using hEqHeight.symm⟩
            | node lc ll lk lr =>
                left
                have hRb' : RootBlack (node lc ll lk lr) := (rootBlack_eq_RootBlack _).mp hlb
                have hbhL := ihL.2.2.1 hRb' (by simp)
                omega
          obtain ⟨hn2, hbal2, hbh2, hfull⟩ := baldL_shape ihL.1 ihL.2.1 hNoRed.2.1 hBalR hdef
          refine ⟨hn2, hbal2, ?_, ?_⟩
          · intro hroot _
            subst hroot; simp [blackHeight]; omega
          · intro hnroot
            have hc : c = Color.red := by
              cases c with
              | black => exact absurd rfl hnroot
              | red => rfl
            have hRootR := (hNoRed.2.2 hc).2
            subst hc
            exact ⟨by simp [blackHeight]; omega, hfull hRootR⟩
        · have hdel : del x (node c l y r) = node Color.red (del x l) y r := by
            simp [del, h1, hlb]
          rw [hdel]
          have hRnb : ¬ RootBlack l := fun hr' => hlb ((rootBlack_eq_RootBlack l).mpr hr')
          have hc : c = Color.black := by
            cases c with
            | black => rfl
            | red => exact absurd (hNoRed.2.2 rfl).1 hRnb
          subst hc
          obtain ⟨hbhL, hnL⟩ := ihL.2.2.2 hRnb
          refine ⟨noRedRed2_node_iff.mpr ⟨hnL, hNoRed.2.1⟩,
            ⟨ihL.2.1, hBalR, by omega⟩, ?_, ?_⟩
          · intro _ _
            simp [blackHeight]; omega
          · intro hnb; exact (hnb rfl).elim
      · by_cases h2 : x > y
        · by_cases hrb : rootBlack r = true
          · have hdel : del x (node c l y r) = baldR l y (del x r) := by
              simp [del, h1, h2, hrb]
            rw [hdel]
            have hdef : blackHeight (del x r) + 1 = blackHeight l ∨
                (del x r = empty ∧ blackHeight l = 0) := by
              cases r with
              | empty =>
                  right
                  exact ⟨by simp [del], by simpa [blackHeight] using hEqHeight⟩
              | node rc rl z rr =>
                  left
                  have hRb' : RootBlack (node rc rl z rr) := (rootBlack_eq_RootBlack _).mp hrb
                  have hbhR := ihR.2.2.1 hRb' (by simp)
                  omega
            obtain ⟨hn2, hbal2, hbh2, hfull⟩ := baldR_shape ihR.1 ihR.2.1 hNoRed.1 hBalL hdef
            refine ⟨hn2, hbal2, ?_, ?_⟩
            · intro hroot _
              subst hroot; simp [blackHeight]; omega
            · intro hnroot
              have hc : c = Color.red := by
                cases c with
                | black => exact absurd rfl hnroot
                | red => rfl
              have hRootL := (hNoRed.2.2 hc).1
              subst hc
              exact ⟨by simp [blackHeight]; omega, hfull hRootL⟩
          · have hdel : del x (node c l y r) = node Color.red l y (del x r) := by
              simp [del, h1, h2, hrb]
            rw [hdel]
            have hRnb : ¬ RootBlack r := fun hr' => hrb ((rootBlack_eq_RootBlack r).mpr hr')
            have hc : c = Color.black := by
              cases c with
              | black => rfl
              | red => exact absurd (hNoRed.2.2 rfl).2 hRnb
            subst hc
            obtain ⟨hbhR, hnR⟩ := ihR.2.2.2 hRnb
            refine ⟨noRedRed2_node_iff.mpr ⟨hNoRed.1, hnR⟩,
              ⟨hBalL, ihR.2.1, by omega⟩, ?_, ?_⟩
            · intro _ _
              simp [blackHeight]
            · intro hnb; exact (hnb rfl).elim
        · have hdel : del x (node c l y r) = join l r := by simp [del, h1, h2]
          rw [hdel]
          by_cases hrE : r = empty
          · subst hrE
            have hj : join l empty = l := by simp [join]
            rw [hj]
            refine ⟨noRedRed2_of_noRedRed hNoRed.1, hBalL, ?_, ?_⟩
            · intro hroot _
              subst hroot; simp [blackHeight]
            · intro hnroot
              have hc : c = Color.red := by
                cases c with
                | black => exact absurd rfl hnroot
                | red => rfl
              subst hc
              exact ⟨by simp [blackHeight], hNoRed.1⟩
          · by_cases hlE : l = empty
            · subst hlE
              have hj : join empty r = r := by simp [join, hrE]
              rw [hj]
              have hbh0 : blackHeight r = 0 := by
                have h2 := hEqHeight.symm; simpa [blackHeight] using h2
              refine ⟨noRedRed2_of_noRedRed hNoRed.2.1, hBalR, ?_, ?_⟩
              · intro hroot _
                subst hroot; simp [blackHeight, hbh0]
              · intro hnroot
                have hc : c = Color.red := by
                  cases c with
                  | black => exact absurd rfl hnroot
                  | red => rfl
                subst hc
                exact ⟨by simp [blackHeight, hbh0], hNoRed.2.1⟩
            · by_cases hrb : rootBlack r = true
              · have hj : join l r = baldR l (splitMin r).1 (splitMin r).2 := by
                  simp [join, hrE, hlE, hrb]
                rw [hj]
                have hRootR : RootBlack r := (rootBlack_eq_RootBlack r).mp hrb
                obtain ⟨hn2s, hbal2s, hbhs, -⟩ := splitMin_invariant hRootedR hrE
                have hdefR : blackHeight (splitMin r).2 + 1 = blackHeight l ∨
                    ((splitMin r).2 = empty ∧ blackHeight l = 0) :=
                  Or.inl (by have h2 := hbhs hRootR; omega)
                obtain ⟨hn2b, hbal2b, hbhb, hfullb⟩ :=
                  baldR_shape hn2s hbal2s hNoRed.1 hBalL hdefR
                refine ⟨hn2b, hbal2b, ?_, ?_⟩
                · intro hroot _
                  subst hroot; simp [blackHeight]; omega
                · intro hnroot
                  have hc : c = Color.red := by
                    cases c with
                    | black => exact absurd rfl hnroot
                    | red => rfl
                  have hRootL := (hNoRed.2.2 hc).1
                  subst hc
                  exact ⟨by simp [blackHeight]; omega, hfullb hRootL⟩
              · have hj : join l r = node Color.red l (splitMin r).1 (splitMin r).2 := by
                  simp [join, hrE, hlE, hrb]
                rw [hj]
                have hRnbR : ¬ RootBlack r :=
                  fun hr' => hrb ((rootBlack_eq_RootBlack r).mpr hr')
                obtain ⟨hn2s, hbal2s, -, hredR⟩ := splitMin_invariant hRootedR hrE
                obtain ⟨hbhR, hnR⟩ := hredR hRnbR
                have hc : c = Color.black := by
                  cases c with
                  | black => rfl
                  | red => exact absurd (hNoRed.2.2 rfl).2 hRnbR
                subst hc
                refine ⟨noRedRed2_node_iff.mpr ⟨hNoRed.1, hnR⟩,
                  ⟨hBalL, hbal2s, by omega⟩, ?_, ?_⟩
                · intro _ _
                  simp [blackHeight]
                · intro hnb; exact (hnb rfl).elim

/-- Deletion preserves the global red-black shape invariant. -/
theorem redBlackShape_delete {x : Nat} {t : RBTree} (h : RedBlackShape t) :
    RedBlackShape (delete x t) := by
  obtain ⟨hn2, hbal, -, -⟩ := del_invariant (redBlackShape_redRootedRB h)
  exact ⟨rootBlack_repaint_black _, hn2, balancedBlackHeight_repaintRoot Color.black hbal⟩

/-- {name}`del` preserves membership for keys different from the deleted key
(forward direction: keys in the result are keys in the original). -/
theorem inTree_del_forward (x q : Nat) (t : RBTree) : InTree q (del x t) → InTree q t := by
  induction t with
  | empty => simp [del, InTree]
  | node c l y r ihl ihr =>
    simp [del]
    by_cases hx_lt_y : x < y
    · simp [hx_lt_y]
      by_cases hrb : rootBlack l
      · simp [hrb, inTree_baldL]
        intro h
        rcases h with (hqy | hql | hqr)
        · exact Or.inl hqy
        · have hqlT := ihl hql
          exact Or.inr (Or.inl hqlT)
        · exact Or.inr (Or.inr hqr)
      · simp [hrb, InTree]
        intro h
        rcases h with (hqy | hql | hqr)
        · exact Or.inl hqy
        · have hqlT := ihl hql
          exact Or.inr (Or.inl hqlT)
        · exact Or.inr (Or.inr hqr)
    · by_cases hx_gt_y : x > y
      · simp [hx_lt_y, hx_gt_y]
        by_cases hrb : rootBlack r
        · simp [hrb, inTree_baldR]
          intro h
          rcases h with (hqy | hql | hqr)
          · exact Or.inl hqy
          · exact Or.inr (Or.inl hql)
          · have hqrT := ihr hqr
            exact Or.inr (Or.inr hqrT)
        · simp [hrb, InTree]
          intro h
          rcases h with (hqy | hql | hqr)
          · exact Or.inl hqy
          · exact Or.inr (Or.inl hql)
          · have hqrT := ihr hqr
            exact Or.inr (Or.inr hqrT)
      · have h_eq : x = y := by omega
        subst h_eq
        simp [inTree_join_iff]
        intro h
        rcases h with (hql | hqr)
        · exact Or.inr (Or.inl hql)
        · exact Or.inr (Or.inr hqr)

/-- {name}`del` preserves membership for keys different from the deleted key
(backward direction: keys in the original (except the deleted key) survive). -/
theorem inTree_del_backward (x q : Nat) (t : RBTree) (h : InTree q t) (hne : q ≠ x) :
    InTree q (del x t) := by
  induction t generalizing x q with
  | empty => simp [InTree] at h
  | node c l y r ihl ihr =>
    simp [del]
    by_cases hx_lt_y : x < y
    · simp [hx_lt_y]
      rcases h with (hqy | hql | hqr)
      · by_cases hrb : rootBlack l
        · simp [hrb, inTree_baldL, hqy]
        · simp [hrb, InTree, hqy]
      · have h_del : InTree q (del x l) := ihl x q hql hne
        by_cases hrb : rootBlack l
        · simp [hrb, inTree_baldL, h_del]
        · simp [hrb, InTree, h_del]
      · by_cases hrb : rootBlack l
        · simp [hrb, inTree_baldL, hqr]
        · simp [hrb, InTree, hqr]
    · by_cases hx_gt_y : x > y
      · simp [hx_lt_y, hx_gt_y]
        rcases h with (hqy | hql | hqr)
        · by_cases hrb : rootBlack r
          · simp [hrb, inTree_baldR, hqy]
          · simp [hrb, InTree, hqy]
        · by_cases hrb : rootBlack r
          · simp [hrb, inTree_baldR, hql]
          · simp [hrb, InTree, hql]
        · have h_del : InTree q (del x r) := ihr x q hqr hne
          by_cases hrb : rootBlack r
          · simp [hrb, inTree_baldR, h_del]
          · simp [hrb, InTree, h_del]
      · have h_eq : x = y := by omega
        subst h_eq
        rcases h with (hqy | hql | hqr)
        · exfalso; exact hne hqy
        · simp [inTree_join_iff, Or.inl hql]
        · simp [inTree_join_iff, Or.inr hqr]

/-- The deleted key is not present in the result of {name}`del` (requires BST). -/
theorem not_inTree_del_self (x : Nat) (t : RBTree) (hbst : BST t) : ¬ InTree x (del x t) := by
  induction t with
  | empty => simp [del, InTree]
  | node c l y r ihl ihr =>
    have ⟨hbstL, hbstR, hLT, hGT⟩ : BST l ∧ BST r ∧ (∀ x, InTree x l → x < y) ∧ (∀ x, InTree x r → y < x) := by
      simp [BST] at hbst; exact hbst
    simp [del]
    by_cases hx_lt_y : x < y
    · simp [hx_lt_y]
      have h_not_in_r : ¬ InTree x r := by
        intro hxr; exact (Nat.lt_asymm hx_lt_y) (hGT x hxr)
      have hx_ne_y : x ≠ y := Nat.ne_of_lt hx_lt_y
      by_cases hrb : rootBlack l
      · simp [hrb]
        rw [inTree_baldL]
        intro h; rcases h with (hxy | hxdl | hxr)
        · exact hx_ne_y hxy
        · exact ihl hbstL hxdl
        · exact h_not_in_r hxr
      · simp [hrb]
        have h_unfold : InTree x (node Color.red (del x l) y r) ↔ (x = y ∨ InTree x (del x l) ∨ InTree x r) := by
          simp [InTree]
        rw [h_unfold]
        intro h; rcases h with (hxy | hxdl | hxr)
        · exact hx_ne_y hxy
        · exact ihl hbstL hxdl
        · exact h_not_in_r hxr
    · by_cases hx_gt_y : x > y
      · simp [hx_lt_y, hx_gt_y]
        have h_not_in_l : ¬ InTree x l := by
          intro hxl
          have hx_lt_y : x < y := hLT x hxl
          exact (Nat.lt_asymm hx_lt_y) hx_gt_y
        have hx_ne_y : x ≠ y := Nat.ne_of_gt hx_gt_y
        by_cases hrb : rootBlack r
        · simp [hrb]
          rw [inTree_baldR]
          intro h; rcases h with (hxy | hxl | hxdr)
          · exact hx_ne_y hxy
          · exact h_not_in_l hxl
          · exact ihr hbstR hxdr
        · simp [hrb]
          have h_unfold : InTree x (node Color.red l y (del x r)) ↔ (x = y ∨ InTree x l ∨ InTree x (del x r)) := by
            simp [InTree]
          rw [h_unfold]
          intro h; rcases h with (hxy | hxl | hxdr)
          · exact hx_ne_y hxy
          · exact h_not_in_l hxl
          · exact ihr hbstR hxdr
      · have h_eq : x = y := by omega
        subst h_eq
        have h_not_in_l : ¬ InTree x l := by
          intro hxl; exact (Nat.lt_irrefl x) (hLT x hxl)
        have h_not_in_r : ¬ InTree x r := by
          intro hxr; exact (Nat.lt_irrefl x) (hGT x hxr)
        simp [inTree_join_iff, h_not_in_l, h_not_in_r]

/-- Full membership-after-{name}`del` equivalence (requires BST). -/
theorem inTree_del_iff (x q : Nat) (t : RBTree) (hbst : BST t) :
    InTree q (del x t) ↔ InTree q t ∧ q ≠ x := by
  constructor
  · intro h; constructor
    · exact inTree_del_forward x q t h
    · intro hqx; subst q; exact not_inTree_del_self x t hbst h
  · intro ⟨h, hne⟩; exact inTree_del_backward x q t h hne

/-- {name}`delete` preserves membership (forward direction). -/
theorem inTree_delete_forward (x q : Nat) (t : RBTree) :
    InTree q (delete x t) → InTree q t := by
  simp [delete, inTree_repaintRoot_iff]; exact inTree_del_forward x q t

/-- {name}`delete` preserves membership for keys different from the deleted key
(backward direction). -/
theorem inTree_delete_backward (x q : Nat) (t : RBTree) (h : InTree q t) (hne : q ≠ x) :
    InTree q (delete x t) := by
  simp [delete, inTree_repaintRoot_iff]; exact inTree_del_backward x q t h hne

/-- The deleted key is not in the result of {name}`delete` (requires BST). -/
theorem not_inTree_delete_self (x : Nat) (t : RBTree) (hbst : BST t) :
    ¬ InTree x (delete x t) := by
  simp [delete, inTree_repaintRoot_iff, not_inTree_del_self x t hbst]

/-- Full membership-after-{name}`delete` equivalence (requires BST). -/
theorem inTree_delete_iff (x q : Nat) (t : RBTree) (hbst : BST t) :
    InTree q (delete x t) ↔ InTree q t ∧ q ≠ x := by
  simp [delete, inTree_repaintRoot_iff, inTree_del_iff x q t hbst]

end RBTree

end Chapter13
end CLRS
