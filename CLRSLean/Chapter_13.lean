import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# Chapter 13 - Red-Black Trees

Chapter 13 proves that red-black trees maintain logarithmic height through
color and black-height invariants.  The current CLRS-Lean pass builds the local
invariant layer: colored trees, membership preservation under rotations, the
no-red-red property, black-height balance, root recoloring, and a bundled local
red-black shape predicate.  It also isolates the four local
{lit}`RB-INSERT-FIXUP` rotation/recoloring cases as small certificates.

## Sections

* 13.1 Red-black trees: {lit}`partial`.
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
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftLeft`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_leftRight`,
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightLeft`, and
  {lit}`CLRS.Chapter13.RBTree.redBlackShape_insertFixup_rightRight`.

## Current Gaps

The full CLRS insertion and deletion algorithms are not yet mechanized.  The
next insertion step is to compose the local fixup certificates into an
executable {lit}`RB-INSERT-FIXUP`; deletion fixup and the logarithmic-height
theorem remain larger future targets.
-/

namespace CLRS
namespace Chapter13
end Chapter13
end CLRS
