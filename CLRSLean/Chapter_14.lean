import CLRSLean.Chapter_14.Section_14_1_Order_Statistic_Trees
import CLRSLean.Chapter_14.Section_14_3_Interval_Trees

/-!
# Chapter 14 - Augmenting Data Structures

Chapter 14 explains how to attach auxiliary information to a data structure and
maintain enough local consistency to support stronger queries.  The first
CLRS-Lean pass formalizes the mathematical core of order-statistic trees: each
node stores a subtree size, and rank selection uses the left-subtree size to
choose a branch.  The rotation layer now exposes cached-root-size preservation,
ideal rank-selection preservation, and the corresponding augmented-selector
wrapper for well-sized trees.  It also exposes a recompute-then-rotate bridge:
from any tree, recomputing size fields before a local rotation produces a
well-sized tree whose augmented selector still agrees with the original ideal
rank selector.

## Sections

* 14.1 Order-statistic trees: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter14.OSTree.storedSize_eq_realSize_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.keys_recomputeSizes`, and
  {lit}`CLRS.Chapter14.OSTree.keys_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.keys_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.realSize_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateLeft_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.storedSize_rotateRight_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateLeft`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_rotateRight`,
  {lit}`CLRS.Chapter14.OSTree.rotateLeft_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rotateRight_wellSized`, and
  {lit}`CLRS.Chapter14.OSTree.osSelect?_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateLeft_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateRight_eq_rankSelect?_of_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.realSize_recomputeSizes`,
  {lit}`CLRS.Chapter14.OSTree.rankSelect?_recomputeSizes`,
  {lit}`CLRS.Chapter14.OSTree.rotateLeft_recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.rotateRight_recomputeSizes_wellSized`,
  {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateLeft_recomputeSizes_eq_rankSelect?`,
  and {lit}`CLRS.Chapter14.OSTree.osSelect?_rotateRight_recomputeSizes_eq_rankSelect?`.
  The size augmentation is now also threaded through an executable red-black
  insertion on the colour-and-size augmented tree {lit}`CLRS.Chapter14.OSRBTree`:
  {lit}`CLRS.Chapter14.OSRBTree.wellSized_insert`,
  {lit}`CLRS.Chapter14.OSRBTree.storedSize_insert`,
  {lit}`CLRS.Chapter14.OSRBTree.osSelect?_insert_eq_rankSelect?`,
  {lit}`CLRS.Chapter14.OSRBTree.toRB_insert`,
  {lit}`CLRS.Chapter14.OSRBTree.redBlackShape_toRB_insert`, and
  {lit}`CLRS.Chapter14.OSRBTree.mem_keys_insert`.
* 14.3 Interval trees: {lit}`proved` for the functional well-augmented BST
  model.
  Main results: {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_some_overlap`,
  {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_none_noOverlap`, and
  {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_spec`.
  It also packages the general augmentation interface: an **arbitrary**
  augmentation threaded through an executable red-black insertion on the generic
  {lit}`CLRS.Chapter14.AugmentedRBTree`, with
  {lit}`CLRS.Chapter14.AugmentedRBTree.wellAugmented_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.toRB_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.redBlackShape_toRB_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.mem_keys_insert`, and the size and
  interval instances
  {lit}`CLRS.Chapter14.AugmentedRBTree.sizeAug_wellAugmented_insert` and
  {lit}`CLRS.Chapter14.AugmentedRBTree.maxHighAug_wellAugmented_insert`.

## Current Gaps

The current model proves the augmentation invariant and rank-selection
correctness for a functional tree, including size-preserving local rotations,
and interval-search correctness for well-augmented BSTs.  The size augmentation
is threaded through an executable red-black insertion via the size-specific
{lit}`OSRBTree`, and the general augmentation interface now threads an
*arbitrary* augmentation through an executable red-black insertion on the generic
{lit}`AugmentedRBTree`: {lit}`AugmentedRBTree.wellAugmented_insert` shows the
invariant survives balancing for any augmentation, and
{lit}`AugmentedRBTree.toRB_insert` shows the augmentation-erasing projection
refines the executable Chapter 13 {lit}`RBTree.insert`; the size and interval
fields are recovered as instances.  The remaining gap is augmentation through
*deletion* (blocked on the Chapter 13 executable red-black deletion loop).
-/

namespace CLRS
namespace Chapter14
end Chapter14
end CLRS
