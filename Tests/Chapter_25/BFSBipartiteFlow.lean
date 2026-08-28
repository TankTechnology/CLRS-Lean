import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution

/-! Focused public-interface checks for the BFS-selected §25.1 flow method. -/

#check CLRS.Matchings.flowArcCount
#check CLRS.Matchings.augmentationAttemptBudget_le
#check CLRS.Matchings.bfsFlowStep
#check CLRS.Matchings.bfsFlowIter_integral
#check CLRS.Matchings.flowRun
#check CLRS.Matchings.flowRun_flow
#check CLRS.Matchings.flowRun_augmentations_le
#check CLRS.Matchings.bfsFlowIter_noAugmentingPath_left_card
#check CLRS.Matchings.flowMatchingAt_size
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_bfs
#check CLRS.Matchings.costedMatchingRun_maximum
#check CLRS.Matchings.costedMatchingRun_work_le_product
#check CLRS.Matchings.flowMethod_finds_maximum_matching_with_attached_cost
