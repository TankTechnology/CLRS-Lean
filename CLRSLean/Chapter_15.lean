import CLRSLean.Chapter_15.Section_15_1_Rod_Cutting
import CLRSLean.Chapter_15.Section_15_2_Matrix_Chain_Multiplication
import CLRSLean.Chapter_15.Section_15_4_Longest_Common_Subsequence
import CLRSLean.Chapter_15.Section_15_5_Optimal_Binary_Search_Trees

/-!
# Chapter 15 - Dynamic Programming

Chapter 15 studies optimal substructure and overlapping subproblems.  The first
CLRS-Lean pass covers four dynamic-programming examples at the mathematical
optimality-interface level: rod cutting, matrix-chain multiplication, LCS, and
optimal binary search trees.  For rod cutting and OBST, the chapter records both
the Bellman recurrence layer and an executable recurrence-valued function.  For
matrix-chain multiplication and LCS, the chapter records table/reconstruction
certificates, recurrence wrappers on certified LCS tables, direct recurrence
consequences for matching and nonmatching LCS heads, and pure executable table
and reconstruction algorithms.  Concrete mutable-array implementations remain
future refinements.

## Sections

* 15.1 Rod cutting: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.bottomUpRodRevenue_rodCutRecurrence`,
  {lit}`CLRS.Chapter15.firstCutValue_le_of_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_table_of_rodCutTableRecurrence`,
  {lit}`CLRS.Chapter15.planValue_le_bottomUpRodRevenue`,
  {lit}`CLRS.Chapter15.rodRevenue_le_of_firstCutValue_bounds`,
  {lit}`CLRS.Chapter15.planValue_le_revenue_of_rodCutRecurrence`, and
  {lit}`CLRS.Chapter15.planValue_le_optimalPlanValue_of_same_length`.
* 15.2 Matrix-chain multiplication: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.matrixChain_opt_le_planCost`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_eq`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_optimal`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_le_planCost`,
  {lit}`CLRS.Chapter15.matrixChain_reconstructed_cost_eq_of_reconstructed`,
  {lit}`CLRS.Chapter15.matrixChainSplit_optimal`,
  {lit}`CLRS.Chapter15.matrixChainReconstruct_reconstructed`, and
  {lit}`CLRS.Chapter15.matrixChain_correct`.
* 15.4 Longest common subsequence: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.LCSCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.LCSCertificate.length_eq_of_certificates`, and
  {lit}`CLRS.Chapter15.isCommonSubsequence_comm`,
  plus {lit}`CLRS.Chapter15.LCSTableRecurrence.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_left`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.nil_right`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_self`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.diagonal_lt_cons_cons_of_eq`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.cons_cons_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.drop_left_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.drop_right_le_of_ne`,
  {lit}`CLRS.Chapter15.LCSTableCertificate.commonSubsequence_length_le`,
  {lit}`CLRS.Chapter15.lcsTable_reconstruction_optimal`,
  {lit}`CLRS.Chapter15.lcsCertificate_of_table_reconstruction_length`, and
  {lit}`CLRS.Chapter15.lcs_correct`.
* 15.5 Optimal binary search trees: {lit}`partial`.
  Main results: {lit}`CLRS.Chapter15.OBST.obst_opt_le_planCost`,
  {lit}`CLRS.Chapter15.OBST.obst_reconstructed_cost_eq`,
  {lit}`CLRS.Chapter15.OBST.obst_reconstructed_optimal`,
  {lit}`CLRS.Chapter15.OBST.bottomUpOBST_obstRecurrence`, and
  {lit}`CLRS.Chapter15.OBST.obst_correct`.

## Current Gaps

The current files prove mathematical optimality interfaces for rod cutting,
matrix-chain multiplication, LCS, and optimal binary search trees.  Rod cutting
and OBST have executable recurrence-valued functions, while matrix chain, LCS,
and OBST expose proved pure reconstruction procedures.  Mutable-array table
construction, memoized mutation, and RAM-cost semantics remain future
refinements.
-/

namespace CLRS
namespace Chapter15
end Chapter15
end CLRS
