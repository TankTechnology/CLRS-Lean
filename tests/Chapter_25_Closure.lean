import CLRSLean.Chapter_25

/-!
# Chapter 25 Closure Test

Verifies that the headline theorems of Chapter 25 are kernel-checked
(no `sorry`/`admit` axioms).  This seals the core milestones of the
all-pairs shortest-paths formalization.
-/

-- Section 25.1: All-Pairs correctness
#check CLRS.Chapter24.WeightedGraph.lemma_25_1
#check CLRS.Chapter24.WeightedGraph.L_sq_eq_minPlusMul

-- Section 25.2: Floyd-Warshall correctness (Theorems 25.7, 25.8, 25.3)
#check CLRS.Chapter24.WeightedGraph.floydWarshall_isShortestDist
#check CLRS.Chapter24.WeightedGraph.D_le_simpleWalk
#check CLRS.Chapter24.WeightedGraph.D_attainable
#check CLRS.Chapter24.WeightedGraph.floydWarshall_nonneg_diag
#check CLRS.Chapter24.WeightedGraph.negative_diagonal_implies_negative_cycle

-- Section 25.3: Johnson reweighting
#check CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg
#check CLRS.Chapter24.WeightedGraph.reweighted_isShortestDist

-- Running-time layer (Floyd-Warshall O(V³), FASTER-APSP O(V³ log V), Johnson O(V² log V + V E log V))
#check CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed
#check CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_cubed_log
#check CLRS.Chapter24.WeightedGraph.johnsonCost_eq

/-!
Axiom checks — each headline theorem must have no `sorry`/`admit` axioms.
-/

#print axioms CLRS.Chapter24.WeightedGraph.floydWarshall_isShortestDist
#print axioms CLRS.Chapter24.WeightedGraph.D_le_simpleWalk
#print axioms CLRS.Chapter24.WeightedGraph.D_attainable
#print axioms CLRS.Chapter24.WeightedGraph.floydWarshall_nonneg_diag
#print axioms CLRS.Chapter24.WeightedGraph.negative_diagonal_implies_negative_cycle
#print axioms CLRS.Chapter24.WeightedGraph.reweightedWeight_nonneg
#print axioms CLRS.Chapter24.WeightedGraph.reweighted_isShortestDist
#print axioms CLRS.Chapter24.WeightedGraph.floydWarshall_O_cubed
#print axioms CLRS.Chapter24.WeightedGraph.fasterAPSPCost_le_n_cubed_log
#print axioms CLRS.Chapter24.WeightedGraph.johnsonCost_eq
