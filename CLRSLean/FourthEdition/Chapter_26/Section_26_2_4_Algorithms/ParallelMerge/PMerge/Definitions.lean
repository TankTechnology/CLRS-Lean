import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMerge.MergeSplit

/-!
# CLRS Chapter 26.3 — Executable P-MERGE

This module implements the pure functional control structure of CLRS P-MERGE.
Each nonempty call selects the midpoint of the longer input, binary-searches
the other input, spawns the lower and upper merges in parallel, and places the
pivot between their outputs.  The definition is total even when the inputs are
not sorted; sortedness is needed only by the later correctness theorem.
-/

namespace CLRS
namespace Chapter27

/-- Parallel merge with execution-attached work and span.

Binary search is sequential, the two recursive subproblems use one parallel
fork/join, and pivot placement is charged one unit of work and span.
-/
def pMerge [LinearOrder α] (xs ys : List α) : Costed (List α) :=
  if hzero : xs.length + ys.length = 0 then
    Costed.pure []
  else
    let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
    Costed.seq S.search fun _ =>
      let lower := pMerge S.lowerPrimary S.lowerSecondary
      let upper := pMerge S.upperPrimary S.upperSecondary
      Costed.seq (Costed.par lower upper) fun parts =>
        Costed.charge 1 1 (parts.1 ++ S.pivot :: parts.2)
termination_by xs.length + ys.length
decreasing_by
  · change S.leftSize < xs.length + ys.length
    calc
      S.leftSize < S.totalSize := S.leftSize_lt
      _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
  · change S.rightSize < xs.length + ys.length
    calc
      S.rightSize < S.totalSize := S.rightSize_lt
      _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]

end Chapter27
end CLRS
