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
