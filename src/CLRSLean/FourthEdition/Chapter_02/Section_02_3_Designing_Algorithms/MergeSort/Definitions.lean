import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.Merge
import CLRSLean.FourthEdition.Chapter_02.Section_02_3_Designing_Algorithms.MergeSort.Compatibility

/-!
# CLRS Section 2.3 - Executable costed merge sort

This module defines the textbook split--recurse--merge execution.  Unlike the
compatibility {lit}`mergeSort` wrapper, its combine step is the Chapter 2
{lit}`mergeWithCost` whose correctness and counters are proved locally.
-/

namespace CLRS
namespace Chapter02

/-- Observable result and accumulated counters of one merge-sort execution. -/
structure MergeSortExecution where
  value : List Nat
  comparisons : Nat
  outputWrites : Nat
  /-- Textbook recurrence work: one unit at a singleton leaf and one unit for
  every output written by a combine call. -/
  work : Nat
deriving DecidableEq, Repr

/--
Executable merge sort using the verified local {lit}`mergeWithCost` at every
combine node.

Inputs of length at least two are split after {lit}`length / 2` elements.  Both
halves are strictly shorter, so input length is a termination measure.
-/
def mergeSortWithCost : List Nat → MergeSortExecution
  | [] => ⟨[], 0, 0, 0⟩
  | [x] => ⟨[x], 0, 0, 1⟩
  | x :: y :: rest =>
      let input := x :: y :: rest
      let middle := input.length / 2
      let leftRun := mergeSortWithCost (input.take middle)
      let rightRun := mergeSortWithCost (input.drop middle)
      let combined := mergeWithCost leftRun.value rightRun.value
      ⟨combined.value,
        leftRun.comparisons + rightRun.comparisons + combined.comparisons,
        leftRun.outputWrites + rightRun.outputWrites + combined.outputWrites,
        leftRun.work + rightRun.work + combined.outputWrites⟩
termination_by input => input.length
decreasing_by
  all_goals
    simp_wf
    omega

/-- Value-only projection of the executable merge-sort run. -/
def mergeSortValue (xs : List Nat) : List Nat :=
  (mergeSortWithCost xs).value

/-- Work extracted from the execution on a canonical list of length {lit}`n`. -/
def mergeSortWork (n : Nat) : Nat :=
  (mergeSortWithCost (List.replicate n 0)).work

end Chapter02
end CLRS
