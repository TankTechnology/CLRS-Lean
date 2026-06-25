import CLRSLean.Chapter_15.Section_15_1_Rod_Cutting
import CLRSLean.Chapter_15.Section_15_2_Matrix_Chain_Multiplication
import CLRSLean.Chapter_15.Section_15_4_Longest_Common_Subsequence

/-!
# Chapter 15 - Dynamic Programming

Chapter 15 studies optimal substructure and overlapping subproblems.  The first
CLRS-Lean pass starts with rod cutting: a revenue function satisfying the
Bellman first-cut recurrence is an upper bound for every concrete cutting plan,
and any plan attaining that bound is optimal among plans of the same total
length.

## Sections

* 15.1 Rod cutting: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.rodRevenue_le_of_firstCutValue_bounds`,
  {lit}`CLRS.Chapter15.planValue_le_revenue_of_rodCutRecurrence`, and
  {lit}`CLRS.Chapter15.planValue_le_optimalPlanValue_of_same_length`.
* 15.2 Matrix-chain multiplication: {lit}`partial`.
  Main result: {lit}`CLRS.Chapter15.matrixChain_opt_le_planCost`.
* 15.4 Longest common subsequence: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.LCSCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.LCSCertificate.length_eq_of_certificates`, and
  {lit}`CLRS.Chapter15.isCommonSubsequence_comm`.

## Current Gaps

The current files prove mathematical optimality interfaces for rod cutting,
matrix-chain multiplication, and LCS.  Bottom-up table construction, memoized
recursion, reconstruction algorithms, and optimal binary search trees are future
section targets.
-/

namespace CLRS
namespace Chapter15
end Chapter15
end CLRS
