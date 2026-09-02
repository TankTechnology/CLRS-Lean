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

* 14.1 Order-statistic trees: {lit}`partial` at the complete fourth-edition
  dynamic-order-statistics interface.
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
* 14.3 Interval trees: {lit}`partial` at the complete fourth-edition interface;
  the static functional well-augmented BST search model is proved.
  Main results: {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_some_overlap`,
  {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_none_noOverlap`, and
  {lit}`CLRS.Chapter14.IntervalTree.intervalSearch?_spec`.
  It also packages the general augmentation interface: an **arbitrary**
  augmentation threaded through an executable red-black insertion on the generic
  {lit}`CLRS.Chapter14.AugmentedRBTree`, with
  {lit}`CLRS.Chapter14.AugmentedRBTree.wellAugmented_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.toRB_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.redBlackShape_toRB_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.mem_keys_insert`,
  {lit}`CLRS.Chapter14.AugmentedRBTree.wellAugmented_delete`, and
  {lit}`CLRS.Chapter14.AugmentedRBTree.toRB_delete`, and the size and
  interval instances
  {lit}`CLRS.Chapter14.AugmentedRBTree.sizeAug_wellAugmented_insert` and
  {lit}`CLRS.Chapter14.AugmentedRBTree.maxHighAug_wellAugmented_insert`.

## Legacy-layer boundary

This third-edition compatibility layer supplies size-field preservation,
OS-SELECT, generic augmentation preservation, and the static interval-search
specification.  The canonical fourth-edition Chapter 17 modules build on it and
now provide OS-RANK with its logarithmic bound, the constant-time-combine update
bound, and the dynamic/static interval-tree search-after-update bridge.  Those
results live under {lit}`CLRSLean.FourthEdition.Chapter_17` rather than being
duplicated here.

A single bundled BST/red-black/augmentation predicate, RAM-level pointer costs,
and a duplicate-low-endpoint policy are optional refinements beyond the
advertised fourth-edition theorem inventory.
-/

namespace CLRS
namespace Chapter14
end Chapter14
end CLRS
