import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.CostedRun

/-!
Interface contract for the Chapter 25 same-execution adjacency-list cost
closure.  The checked declarations jointly attach residual search, path
augmentation, the returned maximum matching, and the `O(VE)` work bound.
-/

#check CLRS.Chapter26.costedResidualBFS_state
#check CLRS.Chapter26.costedResidualBFS_work_le
#check CLRS.Matchings.matchingFlowResidualSupport_covers
#check CLRS.Matchings.matchingCostedBFS_state
#check CLRS.Matchings.augmentMatchingAlong_size
#check CLRS.Matchings.augmentMatchingAlong_work_le
#check CLRS.Matchings.costedMatchingRun_maximum
#check CLRS.Matchings.costedMatchingRun_flow_eq
#check CLRS.Matchings.costedMatchingRun_flow_maximal
#check CLRS.Matchings.costedMatchingRun_flow_integral
#check CLRS.Matchings.costedMatchingRun_work_le
#check CLRS.Matchings.costedMatchingRun_work_le_product
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_attached_cost
