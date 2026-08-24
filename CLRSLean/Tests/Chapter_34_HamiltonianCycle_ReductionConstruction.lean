import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness

namespace CLRS.Tests.Chapter34HamiltonianCycleReductionConstruction

open Chapter34
open Chapter34.HamiltonianCycleReduction

def oneEdgeOneSelector : VertexCoverInstance where
  vertexCount := 2
  targetSize := 1
  edges := [(0, 1)]

def oneEdgeTwoSelectors : VertexCoverInstance where
  vertexCount := 2
  targetSize := 2
  edges := [(0, 1)]

example : oneEdgeOneSelector.WellFormed := by decide

example : incidentOccurrences oneEdgeOneSelector 0 =
    [{ occurrence := 0, rightSide := false }] := by
  decide

example : incidentOccurrences oneEdgeOneSelector 1 =
    [{ occurrence := 0, rightSide := true }] := by
  decide

example : (clrsHamiltonianInstance oneEdgeOneSelector).WellFormed :=
  clrsHamiltonianInstance_wellFormed oneEdgeOneSelector

example : (vertexCoverToHamiltonianInstance oneEdgeTwoSelectors).WellFormed :=
  vertexCoverToHamiltonianInstance_wellFormed oneEdgeTwoSelectors

example : (clrsHamiltonianInstance oneEdgeOneSelector).vertexCount = 13 := by
  decide

example : (clrsHamiltonianInstance oneEdgeOneSelector).edges.length = 18 := by
  decide

example : (clrsHamiltonianInstance oneEdgeOneSelector).ListRepresentsHamiltonianCycle
      [12, 0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5] := by
  decide

example : selectedGlobalWidgetPath oneEdgeOneSelector {0}
      { occurrence := 0, rightSide := false } =
    [0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5] := by
  decide

example : selectedGlobalWidgetPath oneEdgeOneSelector {0, 1}
      { occurrence := 0, rightSide := false } =
    [0, 1, 2, 3, 4, 5] := by
  decide

example : (clrsHamiltonianInstance oneEdgeOneSelector).PathAdjacent
      (selectedGlobalWidgetPath oneEdgeOneSelector {0}
        { occurrence := 0, rightSide := false }) := by
  apply selectedGlobalWidgetPath_pathAdjacent
  show { occurrence := 0, rightSide := false } ∈
    incidentOccurrences oneEdgeOneSelector 0
  decide

/-- The second selector is a genuine unused slot, joined through the selector
clique rather than by padding the source cover. -/
example : (clrsHamiltonianInstance oneEdgeTwoSelectors).ListRepresentsHamiltonianCycle
      [12, 0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5, 13] := by
  decide

#print axioms canonicalHamiltonianYesInstance_hasHamiltonianCycle
#print axioms not_canonicalHamiltonianNoInstance_hasHamiltonianCycle
#print axioms incidenceChainEdges_length_le
#print axioms clrsHamiltonianInstance_wellFormed
#print axioms vertexCoverToHamiltonianInstance_wellFormed
#print axioms endpoints_of_mem_incidentOccurrences
#print axioms selectedWidgetPath_isWidgetPath
#print axioms selectedGlobalWidgetPath_pathAdjacent

end CLRS.Tests.Chapter34HamiltonianCycleReductionConstruction
