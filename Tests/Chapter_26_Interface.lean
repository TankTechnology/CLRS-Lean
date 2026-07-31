import CLRSLean.Chapter_26

/-!
# Chapter 26 Interface Test

This test protects the current partial Chapter 26 surface.  Missing names are
added only when the corresponding definitions or theorems are implemented.
-/

#check CLRS.Chapter26.FlowNetwork
#check CLRS.Chapter26.Flow
#check CLRS.Chapter26.Flow.value
#check CLRS.Chapter26.Flow.netFlowAcrossCut
#check CLRS.Chapter26.Flow.netFlow_eq_value
#check CLRS.Chapter26.Flow.residualCapacity
#check CLRS.Chapter26.Flow.residualEdge
#check CLRS.Chapter26.Flow.augmentingPathReachable
#check CLRS.Chapter26.Flow.hasAugmentingPath
#check CLRS.Chapter26.Flow.isMaximal
#check CLRS.Chapter26.Flow.value_le_cut_capacity
#check CLRS.Chapter26.Flow.maximal_of_noAugmentingPath

#check CLRS.Chapter26.ResidualPathLength
#check CLRS.Chapter26.IsShortestDist
#check CLRS.Chapter26.isShortestDist_self
#check CLRS.Chapter26.IsShortestDist.unique
#check CLRS.Chapter26.isShortestDist_triangle
#check CLRS.Chapter26.ShortestAugmentingPath

#check CLRS.Chapter26.BipartiteGraph
#check CLRS.Chapter26.Matching
#check CLRS.Chapter26.Matching.size
#check CLRS.Chapter26.capFunc
#check CLRS.Chapter26.toFlowNetwork
#check CLRS.Chapter26.matchingFlowFun
#check CLRS.Chapter26.matchingFlowFunSummand
#check CLRS.Chapter26.matchingToFlow
#check CLRS.Chapter26.matchingToFlow_value
#check CLRS.Chapter26.Flow.IsIntegral
#check CLRS.Chapter26.matchingOfIntegralFlow
#check CLRS.Chapter26.matchingOfIntegralFlow_size
#check CLRS.Chapter26.maxMatching_eq_maxFlow_value
#check CLRS.Chapter26.zeroFlow
#check CLRS.Chapter26.augmentOnce
#check CLRS.Chapter26.iterAugment
#check CLRS.Chapter26.exists_noAugmentingPath_iter

#check CLRS.Chapter26.Flow.eq_cutCapacity_implies_maximal
