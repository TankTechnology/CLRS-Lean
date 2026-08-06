import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# Chapter 13 - Red-Black Trees

Chapter 13 proves that red-black trees maintain logarithmic height through
color and black-height invariants.  This pass builds the local invariant layer
(colored trees, membership preservation under rotations, the no-red-red
property, black-height balance, root recoloring, and a bundled local red-black
shape predicate) and then mechanizes the executable insertion algorithm.  It
also keeps the earlier four local {lit}`RB-INSERT-FIXUP` rotation/recoloring
cases as small reusable certificates.

## Sections

* The single legacy source spans fourth-edition §§13.1--13.4.  The color and
  black-height layer, logarithmic-height theorem, and functional insertion and
  deletion key-set/shape layers are proved.
  Main results: {lit}`CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_rotateRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_repaintRoot_iff`,
  {lit}`CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateLeft_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_rotateRight_red_red`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_leftRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insertFixup_rightRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightLeft`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup_rightRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightRight`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_leftLeft_certificate`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_leftRight_certificate`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_rightLeft_certificate`,
  {lit}`CLRS.Chapter13.RBTree.insertFixupLocal_rightRight_certificate`,
  {lit}`CLRS.Chapter13.RBTree.inTree_insert_iff`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insert`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insertFixup`,
  {lit}`CLRS.Chapter13.RBTree.blackHeight_insert`,
  {lit}`CLRS.Chapter13.RBTree.height_log_bound` (CLRS Lemma 13.1),
  {lit}`CLRS.Chapter13.RBTree.inTree_del_forward`,
  {lit}`CLRS.Chapter13.RBTree.inTree_del_backward`,
  {lit}`CLRS.Chapter13.RBTree.not_inTree_del_self`,
  {lit}`CLRS.Chapter13.RBTree.inTree_delete_forward`,
  {lit}`CLRS.Chapter13.RBTree.inTree_delete_backward`,
  {lit}`CLRS.Chapter13.RBTree.inTree_del_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_delete_iff`, and
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_delete`.

## Current Gaps

The composed functional {lit}`delete` now preserves the color/black-height
{lit}`RedBlackShape`, but that predicate intentionally does not include the
separate {lit}`BST` ordering invariant.  BST/inorder preservation for rotations,
insertion, and deletion remains central work, as do refinement bridges from the
textbook pointer-based fixup loops to the functional algorithms and their
logarithmic execution-cost theorems.
-/

namespace CLRS
namespace Chapter13
end Chapter13
end CLRS
