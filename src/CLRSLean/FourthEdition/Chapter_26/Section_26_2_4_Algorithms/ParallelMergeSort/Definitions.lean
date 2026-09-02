import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.PMerge.Definitions

/-!
# CLRS Chapter 26.3 — Executable P-MERGE-SORT

This module implements the pure functional control structure of CLRS
P-MERGE-SORT.  Nontrivial inputs are split at their midpoint, the two halves
are sorted in parallel, and their sorted values are combined by the executable
P-MERGE algorithm.
-/

namespace CLRS
namespace Chapter27

/-- Parallel merge sort with execution-attached work and span.

Lists of length zero or one are returned unchanged, charging one unit per
element.  Larger lists recursively sort their midpoint halves through one
fork/join and then invoke P-MERGE sequentially on the two results.
-/
def pMergeSort [LinearOrder α] (xs : List α) : Costed (List α) :=
  if hsmall : xs.length ≤ 1 then
    Costed.charge xs.length xs.length xs
  else
    let mid := xs.length / 2
    let left := xs.take mid
    let right := xs.drop mid
    Costed.seq (Costed.par (pMergeSort left) (pMergeSort right)) fun sorted =>
      pMerge sorted.1 sorted.2
termination_by xs.length
decreasing_by
  · simp_wf
    omega
  · simp_wf
    omega

end Chapter27
end CLRS
