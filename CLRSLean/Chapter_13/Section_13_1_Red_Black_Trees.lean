import Mathlib

/-!
# CLRS Section 13.1 - Red-black trees

This section starts the red-black-tree development with local invariants and
rotation facts.  It does not yet formalize the full insertion or deletion
algorithms.  Instead it proves reusable lemmas that those algorithms will need:
rotations preserve membership, repainting the root black preserves the no-red-red
property, repainting the root preserves membership, and repainting the root
preserves child black-height balance.  It also proves red-red local repair
certificates and bundles the local red-black shape invariants into one reusable
predicate.

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
- Theorems {lit}`RBTree.redBlackShape_insertFixup_leftLeft`,
  {lit}`RBTree.redBlackShape_insertFixup_leftRight`,
  {lit}`RBTree.redBlackShape_insertFixup_rightLeft`, and
  {lit}`RBTree.redBlackShape_insertFixup_rightRight`: four local
  {lit}`RB-INSERT-FIXUP` rotation/recoloring cases establish the bundled shape
  invariant.
- Theorems {lit}`RBTree.blackHeight_insertFixup_leftLeft`,
  {lit}`RBTree.blackHeight_insertFixup_leftRight`,
  {lit}`RBTree.blackHeight_insertFixup_rightLeft`, and
  {lit}`RBTree.blackHeight_insertFixup_rightRight`: the same four local
  insertion-fixup rewrites preserve the subtree black height needed by a parent
  context.
- Theorems {lit}`RBTree.insertFixupLocal_leftLeft_certificate`,
  {lit}`RBTree.insertFixupLocal_leftRight_certificate`,
  {lit}`RBTree.insertFixupLocal_rightLeft_certificate`, and
  {lit}`RBTree.insertFixupLocal_rightRight_certificate`: the four branch-specific
  facts are bundled behind one local dispatcher and certificate interface.

Current gaps:

- The executable CLRS {lit}`RB-INSERT`, {lit}`RB-INSERT-FIXUP`,
  {lit}`RB-DELETE`, and {lit}`RB-DELETE-FIXUP` algorithms remain future work.
-/

namespace CLRS
namespace Chapter13

/-! ## Colored tree model -/

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

/-! ## Rotations preserve membership -/

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

/-! ## Local red-black invariants -/

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

/-! ## Local insertion-fixup cases -/

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

end RBTree

end Chapter13
end CLRS
