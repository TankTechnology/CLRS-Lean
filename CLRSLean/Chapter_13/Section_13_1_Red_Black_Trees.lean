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
- Theorem {lit}`RBTree.logarithmic_height`: the logarithmic-height theorem
  (CLRS Theorem 13.1) — any red-black tree with n internal nodes has
  height at most 2 log₂(n+1).

Remaining gaps:

- The executable {lit}`RB-DELETE` and {lit}`RB-DELETE-FIXUP` algorithms remain
  future work.
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

/-! **Logarithmic-height theorem** -/

/-- Height of a tree: length of the longest path from root to leaf in edges. -/
def height : RBTree → Nat
  | empty => 0
  | node _ l _ r => 1 + max (height l) (height r)

/-- Number of internal (non-empty) nodes in a tree. -/
def size : RBTree → Nat
  | empty => 0
  | node _ l _ r => 1 + size l + size r

/--
Under the no-red-red and balanced-black-height invariants, the height of a
tree is bounded by twice its black height when the root is black, and by
twice its black height plus one when the root is red.
-/
theorem height_le_blackHeight_bound {t : RBTree}
    (hNoRed : NoRedRed t) (hBal : BalancedBlackHeight t) :
    (RootBlack t → height t ≤ 2 * blackHeight t) ∧
    (¬ RootBlack t → height t ≤ 2 * blackHeight t + 1) := by
  revert hNoRed hBal
  induction t with
  | empty =>
      intro hNoRed hBal
      simp [height, blackHeight, RootBlack]
  | node color l _ r ihl ihr =>
      intro hNoRed hBal
      rcases hNoRed with ⟨hNoRedL, hNoRedR, hColor⟩
      rcases hBal with ⟨hBalL, hBalR, hEqHeight⟩
      have ihl' := ihl hNoRedL hBalL
      have ihr' := ihr hNoRedR hBalR
      rcases ihl' with ⟨ihlRoot, ihlNotRoot⟩
      rcases ihr' with ⟨ihrRoot, ihrNotRoot⟩
      constructor
      · intro hRootBlack
        have hColorBlack : color = Color.black := by
          simp [RootBlack] at hRootBlack
          exact hRootBlack
        subst hColorBlack
        simp [height, blackHeight]
        -- Children may have red roots; use the appropriate bound for each
        have hl_bound' : height l ≤ 2 * blackHeight l + 1 := by
          by_cases hRB : RootBlack l
          · have h := ihlRoot hRB; omega
          · exact ihlNotRoot hRB
        have hr_bound' : height r ≤ 2 * blackHeight r + 1 := by
          by_cases hRB : RootBlack r
          · have h := ihrRoot hRB; omega
          · exact ihrNotRoot hRB
        -- Since blackHeight l = blackHeight r, both are ≤ 2 * blackHeight l + 1
        rw [← hEqHeight] at hr_bound'
        have hmax : max (height l) (height r) ≤ 2 * blackHeight l + 1 :=
          max_le hl_bound' hr_bound'
        -- Goal: 1 + max ≤ 2 * (blackHeight l + 1) = 2 * blackHeight l + 2
        omega
      · intro hNotRootBlack
        have hColorRed : color = Color.red := by
          cases color
          · rfl
          · simp [RootBlack] at hNotRootBlack
        subst hColorRed
        simp [height, blackHeight]
        have hRootL : RootBlack l := (hColor rfl).1
        have hRootR : RootBlack r := (hColor rfl).2
        have hl_bound : height l ≤ 2 * blackHeight l := ihlRoot hRootL
        have hr_bound : height r ≤ 2 * blackHeight r := ihrRoot hRootR
        rw [← hEqHeight] at hr_bound
        have hmax : max (height l) (height r) ≤ 2 * blackHeight l :=
          max_le hl_bound hr_bound
        -- Goal: 1 + max ≤ 2 * blackHeight l + 1
        omega

/--
A tree satisfying balanced black height has at least {lit}`2^bh - 1`
internal nodes, where {lit}`bh` is its black height.
-/
theorem size_ge_two_pow_blackHeight_sub_one {t : RBTree}
    (hBal : BalancedBlackHeight t) : size t ≥ 2 ^ blackHeight t - 1 := by
  induction t with
  | empty =>
      simp [size, blackHeight]
  | node color l _ r ihl ihr =>
      rcases hBal with ⟨hBalL, hBalR, hEqHeight⟩
      have ihl' := ihl hBalL
      have ihr' := ihr hBalR
      simp [size, blackHeight]
      have hsum : size l + size r ≥ 2 * (2 ^ blackHeight l) - 2 := by
        have hL : size l ≥ 2 ^ blackHeight l - 1 := ihl'
        have hR : size r ≥ 2 ^ blackHeight l - 1 := by
          simpa [hEqHeight] using ihr'
        omega
      by_cases hc : color = Color.black
      · simp [hc]
        have h_pow : 2 ^ (blackHeight l + 1) = 2 * (2 ^ blackHeight l) := by
          simp [Nat.pow_succ, mul_comm]
        have : 1 + size l + size r ≥ 2 ^ (blackHeight l + 1) - 1 := by
          omega
        omega
      · simp [hc]
        have : 1 + size l + size r ≥ 2 ^ blackHeight l - 1 := by
          omega
        omega

/--
The logarithmic-height theorem (CLRS Theorem 13.1): any red-black tree with
n internal nodes has height at most 2 log₂(n+1).
-/
theorem logarithmic_height {t : RBTree} (hShape : RedBlackShape t) :
    height t ≤ 2 * Nat.log2 (size t + 1) := by
  rcases hShape with ⟨hRootBlack, hNoRed, hBal⟩
  have hHeightBound := height_le_blackHeight_bound hNoRed hBal
  rcases hHeightBound with ⟨hRootCase, _⟩
  have hHeight : height t ≤ 2 * blackHeight t := hRootCase hRootBlack
  have hSize : size t ≥ 2 ^ blackHeight t - 1 := size_ge_two_pow_blackHeight_sub_one hBal
  -- From hSize: size t + 1 ≥ 2 ^ blackHeight t
  have hSize' : 2 ^ blackHeight t ≤ size t + 1 := by omega
  -- Using Nat.le_log2: if 2^k ≤ n and n ≠ 0, then k ≤ Nat.log2 n
  have hLog : blackHeight t ≤ Nat.log2 (size t + 1) := by
    have hpos : size t + 1 ≠ 0 := by omega
    exact ((Nat.le_log2 hpos).mpr hSize')
  omega

end RBTree

end Chapter13
end CLRS
