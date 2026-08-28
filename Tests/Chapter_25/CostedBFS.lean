import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.CostedBFS

/-!
Focused interface test for the support-indexed matching BFS and the exact
parent-path translation used by the attached-cost flow execution.
-/

#check CLRS.Matchings.matchingFlowSupportsResidual
#check CLRS.Matchings.matchingCostedBFS_state
#check CLRS.Matchings.matchingCostedBFS_work_le
#check CLRS.Matchings.matchingBFSPathRecovery
#check CLRS.Matchings.matchingBFSPathRecovery_vertices
#check CLRS.Matchings.matchingBFSPathRecovery_work
#check CLRS.Matchings.augmentingPath_of_residualPath
#check CLRS.Matchings.augmentingPath_of_matchingBFSPathRecovery
