import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Model
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Step
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Run
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Refinement

/-!
# BFS flow execution for maximum bipartite matching

Public facade for the target adjacency-list budget, BFS-selected augmentation
run, and integral matching refinement.  The budget is not yet attached to an
adjacency-list implementation, so this facade does not advertise `O(VE)`.
-/
