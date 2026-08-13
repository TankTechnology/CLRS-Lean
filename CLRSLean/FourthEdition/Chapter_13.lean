import CLRSLean.Chapter_13
import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations
import CLRSLean.FourthEdition.Chapter_13.Section_13_3_Insertion
import CLRSLean.FourthEdition.Chapter_13.Section_13_4_Deletion

/-!
# Chapter 13 — Red-Black Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_13`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The legacy color/black-height invariant, logarithmic-height theorem, and
functional insertion/deletion developments are reused, and three fourth-edition
section layers complete the remaining §13.2–§13.4 boundaries:

- §13.2 ({lit}`Section_13_2_Rotations`): a pointer/sentinel red-black store
  {lit}`RBStore` with representation predicate {lit}`StoreRepr`, pointer-level
  rotation/recolor primitives with constant cost, and BST/inorder preservation
  of rotations.
- §13.3 ({lit}`Section_13_3_Insertion`): the {lit}`RB-INSERT-FIXUP` inorder
  bridge ({lit}`keys_balanceLeft`/`keys_balanceRight`), BST output preservation
  {lit}`bst_insert`, and the logarithmic execution-cost theorem
  {lit}`insertCost_log_bound`.
- §13.4 ({lit}`Section_13_4_Deletion`): the logarithmic execution-cost theorem
  {lit}`deleteCost_log_bound` and BST ordering preservation of the composed
  delete {lit}`bst_delete`.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
