import CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray
import CLRSLean.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem

/-!
# Chapter 4. Divide-and-Conquer

Chapter 4 has several good Lean targets.  The current first pass contains both
an algorithmic specification for the maximum-subarray problem and the recurrence
proof infrastructure used by later divide-and-conquer analyses.  Sections 4.3
and 4.4 provide the proof-method infrastructure used by the Master-method file
and by future divide-and-conquer runtime proofs.

* Section 4.1 - The maximum-subarray problem: {lit}`proved` for the exhaustive
  finite-search specification, the CLRS crossing helper, and the
  executable left/right/crossing combine step.
  The file proves that the candidate enumerator contains exactly the nonempty
  contiguous subarrays, and that {lit}`maxSubarray` returns a candidate with
  maximum sum.  It also proves that {lit}`maxCrossingSubarray` returns a
  maximum-sum candidate among all candidates crossing a split.  Finally,
  {lit}`subarray_append_left_or_right_or_crossing` and
  {lit}`subarray_append_optimal_of_cases` provide the proof interface for the
  recursive combine step, and {lit}`maxSubarrayDivideStep_correct` proves the
  executable combine step itself.  The remaining refinement target is a full
  recursive selector and runtime proof against this specification.
* Section 4.2 - Strassen's algorithm for matrix multiplication:
  {lit}`future-work`.
  This is formalizable as block-matrix algebra plus a proof that the seven
  products reconstruct ordinary matrix multiplication.
* Section 4.3 - The substitution method: {lit}`proved` for one-step recurrence
  bounds.
  The file proves upper-bound, lower-bound, sandwich, linear, and geometric
  substitution templates.
* Section 4.4 - The recursion-tree method: {lit}`proved` for additive finite level
  expansions.
  The file proves exact unrolling into level-cost sums and envelope bounds for
  the resulting finite sums.
* Section 4.5 - The master method: {lit}`proved` for exact-power recurrences.
  The file proves the normalized recurrence expansion and three Master-style
  exact-power criteria for bounded, constant, and tail-dominated normalized
  forcing.
* Section 4.6 - Proof of the master theorem: {lit}`future-work`.
  The exact-power proof is the current compiler-clean core.  The full textbook
  theorem for all natural input sizes still needs monotone recurrence models,
  floor/ceiling sandwiching, and a cleaner statement of regularity hypotheses.
-/

namespace CLRS
namespace Chapter04
end Chapter04
end CLRS
