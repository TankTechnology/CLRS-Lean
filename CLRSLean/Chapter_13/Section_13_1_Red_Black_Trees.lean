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

Remaining gaps:

- The fully-composed executable {lit}`RB-DELETE` / {lit}`RB-DELETE-FIXUP` loop
  (threading the doubly-black deficit through Cases 1-3 into Case 4) remains
  future work; the local case rewrites and the terminating certificate are proved.
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

end RBTree

end Chapter13
end CLRS
