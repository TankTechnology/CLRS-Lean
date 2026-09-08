import CLRSLean.FourthEdition.Chapter_17.Section_17_3_Interval_Trees.CachedInsertion
import CLRSLean.FourthEdition.Chapter_17.Section_17_2_Augmenting_Data_Structures.Execution
import CLRSLean.FourthEdition.Chapter_17.Section_17_1_Dynamic_Order_Statistics.RankCardinality
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
content, with the following fourth-edition semantic and execution interfaces:

- §17.1 ({lit}`Section_17_1_Dynamic_Order_Statistics`): OS-RANK
  {lit}`osRank`/{lit}`rankOf` and their agreement on well-sized trees. Strict
  BST ordering identifies rank with the cardinality of keys below the query,
  including absent queries. The query descent has a logarithmic height bound.
- §17.2 ({lit}`Section_17_2_Augmenting_Data_Structures`): actual cached-field
  insertion and rotation execution refines the legacy update on well-augmented
  inputs. It counts at most {lit}`5h+1` combine calls and {lit}`2h` rotations.
  The old {lit}`augmentation_update_bound` is only an abstract height budget;
  no counted cached deletion or allocator-runtime theorem is supplied.
- §17.3 ({lit}`Section_17_3_Interval_Trees`): the dynamic/static interval-tree
  bridge {lit}`toIntervalTree`/{lit}`wellAugmented_toIntervalTree`,
  full-interval lexicographic insertion preserving membership and BST order,
  post-insert overlap search correctness, and the Interval-keyed logarithmic
  query descent bound. Equal low endpoints with different high endpoints are
  distinct keys; only an exactly repeated interval is suppressed.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
