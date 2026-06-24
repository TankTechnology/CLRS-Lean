import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# Chapter 13 - Red-Black Trees

Chapter 13 proves that red-black trees maintain logarithmic height through
color and black-height invariants.  The current CLRSLean pass builds the local
invariant layer: colored trees, membership preservation under rotations, the
no-red-red property, black-height balance, and root recoloring.

## Sections

* 13.1 Red-black trees: `partial`.
  Main results: {lit}`CLRS.Chapter13.RBTree.inTree_rotateLeft_iff`,
  {lit}`CLRS.Chapter13.RBTree.inTree_rotateRight_iff`,
  {lit}`CLRS.Chapter13.RBTree.noRedRed_repaint_black`,
  {lit}`CLRS.Chapter13.RBTree.balancedBlackHeight_repaintRoot`.

## Current Gaps

The full CLRS insertion and deletion algorithms are not yet mechanized.  They
need a balancing representation and a sequence of local-rotation lemmas that
preserve all red-black invariants simultaneously.
-/

namespace CLRS
namespace Chapter13
end Chapter13
end CLRS
