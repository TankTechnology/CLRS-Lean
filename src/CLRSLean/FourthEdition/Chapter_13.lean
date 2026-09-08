import CLRSLean.FourthEdition.Chapter_13.Section_13_1_Red_Black_Trees
import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations
import CLRSLean.FourthEdition.Chapter_13.Section_13_3_Insertion
import CLRSLean.FourthEdition.Chapter_13.Section_13_4_Deletion
import CLRSLean.FourthEdition.Chapter_13.WellFormed

/-!
# Chapter 13 — Red-Black Trees

Native fourth-edition chapter guide.

## Current source

This guide sources fourth-edition §13.1–§13.4 from the native section modules
under {lit}`CLRSLean.FourthEdition.Chapter_13`.  Declarations retain the
{lit}`CLRS.Chapter13` namespace; the legacy import {lit}`CLRSLean.Chapter_13`
and its {lit}`Section_13_1_Red_Black_Trees` module forward to these sources
during the compatibility period.

## Coverage boundary

The native color/black-height invariant layer and logarithmic-height theorem
(§13.1) are complemented by the following represented interfaces:

- §13.1 ({lit}`Section_13_1_Red_Black_Trees`): the color and black-height
  invariants, membership preservation under rotations, the no-red-red property,
  the {lit}`height_log_bound` theorem (CLRS Lemma 13.1), and the functional
  insertion/deletion key-set and shape layers.
- §13.2 ({lit}`Section_13_2_Rotations`): a pointer/sentinel red-black store
  {lit}`RBStore` with parent-aware disjoint-footprint representation and unique
  tree interpretation. Pointer rotations reconnect the root or old parent's
  child and refine functional rotation through arbitrary tree contexts.
  The six-assignment rotation budget is an upper bound, not an exact count.
- §13.3 ({lit}`Section_13_3_Insertion`): inorder and BST preservation for the
  functional Okasaki balancers and insertion. {lit}`insertCost_log_bound` bounds
  a separate search-descent budget; it does not measure complete insertion.
- §13.4 ({lit}`Section_13_4_Deletion`): BST ordering preservation for functional
  deletion. {lit}`deleteCost_log_bound` bounds a search/subtree-height budget;
  join, rebalancing, and pointer execution are not connected to that budget.
- The chapter-level {lit}`WellFormed` bundle combines {lit}`RedBlackShape` and
  {lit}`BST`; {lit}`insert_correct` and {lit}`delete_correct` preserve that
  invariant together with exact membership semantics.

## Implementation details

The bundled client interface is available at
[Shape and BST correctness](CLRSLean/FourthEdition/Chapter_13/WellFormed/).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
