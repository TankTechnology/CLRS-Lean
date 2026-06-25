import CLRSLean.Chapter_14.Section_14_1_Order_Statistic_Trees

/-!
# Chapter 14 - Augmenting Data Structures

Chapter 14 explains how to attach auxiliary information to a data structure and
maintain enough local consistency to support stronger queries.  The first
CLRS-Lean pass formalizes the mathematical core of order-statistic trees: each
node stores a subtree size, and rank selection uses the left-subtree size to
choose a branch.

## Sections

* 14.1 Order-statistic trees: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.keys_recomputeSizes`, and
  {lit}`CLRS.Chapter14.OSTree.osSelect?_eq_rankSelect?_of_wellSized`.

## Current Gaps

The current model proves the augmentation invariant and rank-selection
correctness for a functional tree.  It does not yet formalize rotations,
red-black balancing, interval trees, or the full augmentation theorem from the
textbook.
-/

namespace CLRS
namespace Chapter14
end Chapter14
end CLRS
