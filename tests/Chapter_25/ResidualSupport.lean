import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.ResidualSupport

#check CLRS.Matchings.matchingFlowForwardSupport
#check CLRS.Matchings.matchingFlowResidualSupport
#check CLRS.Matchings.matchingFlowForwardSupport_card
#check CLRS.Matchings.matchingFlowResidualSupport_card
#check CLRS.Matchings.matchingFlowResidualSupport_covers
#check CLRS.Matchings.matchingFlowAdjacency_residualAdj

namespace CLRS.Matchings.ResidualSupportTest

open Finset Chapter26

def oneEdgeGraph : BipartiteGraph (Fin 2) where
  L := {0}
  R := {1}
  h_disjoint := by decide
  h_cover := by decide
  E := {(0, 1)}
  hE_subset := by decide

example : (matchingFlowForwardSupport oneEdgeGraph).card = 3 := by
  rw [matchingFlowForwardSupport_card]
  decide

example : (matchingFlowResidualSupport oneEdgeGraph).card = 6 := by
  rw [matchingFlowResidualSupport_card]
  decide

example : (matchingFlowAdjacency oneEdgeGraph).work = 6 := by
  rw [matchingFlowAdjacency_work]
  decide

end CLRS.Matchings.ResidualSupportTest
