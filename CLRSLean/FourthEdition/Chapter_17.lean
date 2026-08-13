import CLRSLean.Chapter_14
import CLRSLean.FourthEdition.Chapter_17.Section_17_1_Dynamic_Order_Statistics
import CLRSLean.FourthEdition.Chapter_17.Section_17_2_Augmenting_Data_Structures
import CLRSLean.FourthEdition.Chapter_17.Section_17_3_Interval_Trees

/-!
# Chapter 17 — Augmenting Data Structures

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_14`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The third-edition Chapter 14 developments supply substantial relocated proof
content, and three fourth-edition section layers close the §17.1–§17.3
boundaries:

- §17.1 ({lit}`Section_17_1_Dynamic_Order_Statistics`): OS-RANK
  {lit}`osRank`/{lit}`rankOf`, their agreement on well-sized trees, and the
  {lit}`O(log n)` query bound {lit}`osRankCost_log_bound`.
- §17.2 ({lit}`Section_17_2_Augmenting_Data_Structures`): the constant-time
  `combine` premise and the asymptotic augmentation update bound
  {lit}`augmentation_update_bound`.
- §17.3 ({lit}`Section_17_3_Interval_Trees`): the dynamic/static interval-tree
  bridge {lit}`toIntervalTree`/{lit}`wellAugmented_toIntervalTree` and
  search-after-update {lit}`intervalSearch_after_update`, with the search-cost
  foundation {lit}`intervalSearchCost_le_height`.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
