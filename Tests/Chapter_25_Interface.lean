import CLRSLean.Chapter_25

/-!
# Chapter 25 Interface Test

Verifies that all public declarations of Chapter 25 are accessible to
downstream users.
-/

-- Section 25.1: All-Pairs Shortest Paths Model
#check CLRS.Chapter24.WeightedGraph.weightMatrix
#check CLRS.Chapter24.WeightedGraph.minPlusMul
#check CLRS.Chapter24.WeightedGraph.extendShortestPaths
#check CLRS.Chapter24.WeightedGraph.L
#check CLRS.Chapter24.WeightedGraph.fasterAPSP
#check CLRS.Chapter24.WeightedGraph.lemma_25_1
#check CLRS.Chapter24.WeightedGraph.L_sq_eq_minPlusMul
#check CLRS.Chapter24.WeightedGraph.minPlusMulCost
#check CLRS.Chapter24.WeightedGraph.fasterAPSPCost
#check CLRS.Chapter24.WeightedGraph.numSquarings_le_log2_add_one
#check CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_cubed_log
#check CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_four

-- Section 25.2: Floyd-Warshall Algorithm
#check CLRS.Chapter24.WeightedGraph.fwStep
#check CLRS.Chapter24.WeightedGraph.D
#check CLRS.Chapter24.WeightedGraph.floydWarshall
#check CLRS.Chapter24.WeightedGraph.Through
#check CLRS.Chapter24.WeightedGraph.D_le_simpleWalk
#check CLRS.Chapter24.WeightedGraph.floydWarshall_le_walk
#check CLRS.Chapter24.WeightedGraph.D_attainable
#check CLRS.Chapter24.WeightedGraph.floydWarshall_isShortestDist

-- Predecessor matrix and path reconstruction (issue #95)
#check CLRS.Chapter24.WeightedGraph.Pi
#check CLRS.Chapter24.WeightedGraph.Pi_adj
#check CLRS.Chapter24.WeightedGraph.floydWarshallPi
#check CLRS.Chapter24.WeightedGraph.fwReconstructPath

-- Negative-cycle detection (CLRS Theorem 25.3, issue #95)
#check CLRS.Chapter24.WeightedGraph.floydWarshall_nonneg_diag
#check CLRS.Chapter24.WeightedGraph.negative_diagonal_implies_negative_cycle
#check CLRS.Chapter24.WeightedGraph.fwStepCost
#check CLRS.Chapter24.WeightedGraph.floydWarshallCost
#check CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed

-- Section 25.3: Johnson's Algorithm
#check CLRS.Chapter24.WeightedGraph.johnsonAugmentedGraph
#check CLRS.Chapter24.WeightedGraph.reweightedGraph
#check CLRS.Chapter24.WeightedGraph.reweightedWeight
#check CLRS.Chapter24.WeightedGraph.reweightedWalkWeight_eq
#check CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg
#check CLRS.Chapter24.WeightedGraph.reweighted_isShortestDist
#check CLRS.Chapter24.WeightedGraph.johnsonAugmentedGraph_edges_card
#check CLRS.Chapter24.WeightedGraph.johnsonCost
#check CLRS.Chapter24.WeightedGraph.johnsonCost_eq
#check CLRS.Chapter24.WeightedGraph.johnsonCost_le
