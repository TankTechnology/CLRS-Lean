import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S1_CostModel
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S2_Recurrences
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMergeSort

/-!
# 26.3. Parallel Merge Sort

This is the canonical fourth-edition reader page for P-MERGE and
P-MERGE-SORT.  It directly exposes their executable definitions, correctness
proofs, and work and span theorems imported above.

## Formalized content

{name}`CLRS.Chapter27.pMerge_correct` proves sortedness, permutation, and exact
output length for P-MERGE.  Its pointwise work bounds establish linear work,
and its universal span bound is paired with a matching interleaved witness
family.

{name}`CLRS.Chapter27.pMergeSort_correct` proves that P-MERGE-SORT returns a
sorted permutation of every input.  Exact step equations connect the carried
costs to the recurrence.  The pointwise work bounds prove executable
{lit}`Theta(n log n)` work; the universal span upper bound and recursive witness
family give the matching cubic-logarithmic span characterization for this
model.

Status: `proved` for the executable merge and merge-sort development and its
stated cost model.
-/
