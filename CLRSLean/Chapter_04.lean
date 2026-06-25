import CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray
import CLRSLean.Chapter_04.Section_04_2_Strassen_Algorithm
import CLRSLean.Chapter_04.Section_04_3_Substitution_Method
import CLRSLean.Chapter_04.Section_04_4_Recursion_Tree_Method
import CLRSLean.Chapter_04.Section_04_5_Master_Theorem
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

/-!
# Chapter 4. Divide-and-Conquer

Chapter 4 has several good Lean targets.  The current first pass contains both
an algorithmic specification for the maximum-subarray problem and the recurrence
proof infrastructure used by later divide-and-conquer analyses.  Sections 4.3
and 4.4 provide the proof-method infrastructure used by the Master-method file
and by future divide-and-conquer runtime proofs.

* Section 4.1 - The maximum-subarray problem: {lit}`proved` for the current
  functional correctness model.
  The file proves that the candidate enumerator contains exactly the nonempty
  contiguous subarrays, and that {lit}`maxSubarray` returns a candidate with
  maximum sum.  It also proves that {lit}`maxCrossingSubarray` returns a
  maximum-sum candidate among all candidates crossing a split.  Finally,
  {lit}`subarray_append_left_or_right_or_crossing` and
  {lit}`subarray_append_optimal_of_cases` provide the proof interface for the
  recursive combine step, and {lit}`maxSubarrayDivideStep_correct` proves the
  executable combine step itself.  The recursive layer is captured by
  {lit}`maxSubarrayDivideTree_correct` for explicit split trees and
  {lit}`maxSubarrayDivideFuel_correct` for a fuelled midpoint splitter.  The
  remaining refinement target is runtime/RAM-cost analysis.
* Section 4.2 - Strassen's algorithm for matrix multiplication:
  {lit}`proved` for 2 by 2 block algebra.
  The file proves {lit}`CLRS.Chapter04.strassen2x2_correct`: Strassen's seven
  products reconstruct ordinary 2 by 2 block matrix multiplication over an
  arbitrary ring.
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
* Section 4.6 - Proof of the master theorem: {lit}`partial`.
  The file proves floor/ceiling all-input recurrence interfaces, extracts
  exact-power recurrences from those models, and proves a compiler-clean
  transfer bridge from exact-power {lit}`O`, {lit}`Ω`, and {lit}`Θ` bounds to
  all natural inputs under monotone cost and explicit power-sandwich
  hypotheses.  It also proves the adjacent-power {lit}`Nat.log` interval and a
  direct {lit}`allInput_bigTheta_of_powerStep` theorem that discharges those
  sandwich hypotheses from monotone comparison scales with eventual one-step
  control.  The discrete {lit}`criticalPowerScale` and
  {lit}`criticalPowerLogScale` and {lit}`tailDominatedScale` wrappers now turn
  exact-power {lit}`T(b^i) = Θ(a^i)`, {lit}`T(b^i) = Θ((i+1)a^i)`, and
  tail-dominated bounds into all-input bounds, and Section 4.6 packages the
  floor/ceiling recurrence forms of exact-power Master cases 1, 2, and 3 for
  these discrete scales.  It also proves the natural-exponent comparison
  layer for {lit}`a = b^p`, exposing case-1 results as {lit}`Θ(n^p)` and
  case-2 results as {lit}`Θ((⌊log_b n⌋+1)n^p)`.  A real-log bridge
  {name}`CLRS.Chapter04.criticalPowerScale_isBigTheta_realLogScale` now
  connects the discrete scale {lit}`a^(⌊log_b n⌋)` to the textbook scale
  {lit}`n^(log_b a)` for all {lit}`a ≥ 1` and {lit}`b > 1`, so case-1
  and case-2 all-input Master wrappers compose with this bridge to yield
  CLRS-facing {lit}`Θ(n^(log_b a))` bounds.  The remaining gap is a similarly
  textbook-facing case-3 comparison scale.
-/

namespace CLRS
namespace Chapter04
end Chapter04
end CLRS
