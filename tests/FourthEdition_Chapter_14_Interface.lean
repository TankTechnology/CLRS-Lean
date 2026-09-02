import CLRSLean.FourthEdition.Chapter_14

/-!
# Fourth-edition Chapter 14 interface checks

These checks pin the public theorem interface of the native fourth-edition
sections §14.1 (rod cutting), §14.2 (matrix-chain), §14.3 (elements of DP),
§14.4 (LCS), and §14.5 (optimal BST).
-/

namespace CLRS
namespace Chapter15

-- §14.1 Rod cutting
#check rodCutFirstCut
#check rodCutFirstCut_value
#check rodCutPlan
#check rodCutPlan_correct
#check rodCutPlan_optimal
#check rodCutStepCount
#check rodCutStepCount_eq
#check rodCutStepCount_le_quadratic
#check ConsistentCache
#check memoizedRodCut
#check memoizedRodCut_correct
#check memoizedRodCut_value

-- §14.2 Matrix-chain multiplication
#check matrixChainSpace
#check matrixChainSpace_le_square
#check matrixChainTime
#check matrixChainTime_le_cubic

-- §14.3 Elements of dynamic programming
#check MemoCacheConsistent
#check MemoCacheConsistent_eq
#check distinctCacheStates
#check distinctCacheStates_le_length

-- §14.4 Longest common subsequence
#check lcsTableCells
#check lcsTableCells_le_four_mn

-- §14.5 Optimal binary search trees
#check OBST.obstRoot
#check OBST.obstRoot_optimal
#check OBST.obstReconstruct
#check OBST.obstReconstruct_reconstructed
#check OBST.obstTableSpace_le_square
#check OBST.obstTableTime_le_cubic

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms rodCutPlan_optimal
#print axioms memoizedRodCut_correct
#print axioms matrixChainTime_le_cubic
#print axioms OBST.obstRoot_optimal
#print axioms OBST.obstReconstruct_reconstructed

end Chapter15
end CLRS
