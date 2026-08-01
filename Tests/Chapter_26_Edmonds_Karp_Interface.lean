import CLRSLean.Chapter_26

/-!
# Chapter 26 Edmonds--Karp Interface Test

This test protects the concrete shortest-path and augmentation-edge foundation,
the headline monotonicity theorem of CLRS Lemma 26.7, the explicit
shortest-path construction and Edmonds-Karp loop, and the `O(VE²)` counting
theorems of the work analysis.
-/

#check CLRS.Chapter26.Flow.ResidualPath.edges_length
#check CLRS.Chapter26.Flow.ResidualPath.exists_index_of_mem_edges
#check CLRS.Chapter26.ResidualPathLength.trans
#check CLRS.Chapter26.IsShortestDist.exists_predecessor
#check CLRS.Chapter26.ShortestAugmentingPath.prefix_path
#check CLRS.Chapter26.ShortestAugmentingPath.suffix_path
#check CLRS.Chapter26.ShortestAugmentingPath.shortest_prefix
#check CLRS.Chapter26.Flow.augment_residualCapacity
#check CLRS.Chapter26.Flow.AugmentingPath.reverse_mem_edges_of_new_residualEdge
#check CLRS.Chapter26.ShortestAugmentingPath.exists_shortestDist_le_augment
#check CLRS.Chapter26.shortest_path_nondec
#check CLRS.Chapter26.exists_shortest_augmenting_path
#check CLRS.Chapter26.shortestAugmentingPath_iff_hasAugmentingPath
#check CLRS.Chapter26.edmondsKarp_maximal
#check CLRS.Chapter26.criticalAt_growth
#check CLRS.Chapter26.criticalAt_growth_strict
#check CLRS.Chapter26.critical_count_bound
#check CLRS.Chapter26.augmentation_count_bound

namespace CLRS.Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

example (φ : Flow V G) (p : ShortestAugmentingPath φ)
    {v : V} {d d' : ℕ}
    (hd : IsShortestDist φ G.s v d)
    (hd' : IsShortestDist (φ.augment p.path) G.s v d') :
    d ≤ d' :=
  shortest_path_nondec φ p hd hd'

end CLRS.Chapter26

#print axioms CLRS.Chapter26.shortest_path_nondec
#print axioms CLRS.Chapter26.augmentation_count_bound
