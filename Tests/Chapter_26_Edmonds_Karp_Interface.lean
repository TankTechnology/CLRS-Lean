import CLRSLean.Chapter_26

/-!
# Chapter 26 Edmonds--Karp Interface Test

This test protects the concrete shortest-path and augmentation-edge foundation
needed by CLRS Lemma 26.7.  The headline monotonicity theorem is added in the
next RED/GREEN checkpoint.
-/

#check CLRS.Chapter26.Flow.ResidualPath.edges_length
#check CLRS.Chapter26.Flow.ResidualPath.exists_index_of_mem_edges
#check CLRS.Chapter26.ResidualPathLength.trans
#check CLRS.Chapter26.IsShortestDist.exists_predecessor
#check CLRS.Chapter26.ShortestAugmentingPath.shortest_prefix
#check CLRS.Chapter26.Flow.augment_residualCapacity
#check CLRS.Chapter26.Flow.AugmentingPath.reverse_mem_edges_of_new_residualEdge
