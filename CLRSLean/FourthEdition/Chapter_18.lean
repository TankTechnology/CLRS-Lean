import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model.Search
import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model.HeightBound
import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model.RunningTime
import CLRSLean.FourthEdition.Chapter_18.Section_18_2_B_Tree_Insertion
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Invariant
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Rotation
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Repair
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Preservation
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Reassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.MergeReassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.RotationBounds
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.RotationReassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Exact
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Subset
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.SameDepthHeight
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Sorted
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ChildBounded
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Occupancy
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed

/-!
# Chapter 18 — B-Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 18.1--18.3 are native fourth-edition sections (definition of B-trees,
basic operations on B-trees, and deleting a key from a B-tree), imported
directly from
[Section 18.1](CLRSLean/FourthEdition/Chapter_18/Section_18_1_B_Tree_Model/),
[Section 18.2](CLRSLean/FourthEdition/Chapter_18/Section_18_2_B_Tree_Insertion/),
and
[Section 18.3](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/).
Section 18.1 includes the nested search, height-bound, and running-time
developments; section 18.3 includes the nested deletion-invariant and
reassembly developments.  Declarations retain the `CLRS.Chapter18` namespace
during the compatibility period; the third-edition-numbered imports
{lit}`CLRSLean.Chapter_18` and {lit}`CLRSLean.Chapter_18.Section_18_*`
forward to these sources.

## Coverage boundary

The existing B-tree search insertion deletion and invariant developments are reused.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
