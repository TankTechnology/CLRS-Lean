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

def twoEdgesOneSelector : VertexCoverInstance where
  vertexCount := 3
  targetSize := 1
  edges := [(0, 1), (0, 2)]

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

example : selectedSourceVertexPath twoEdgesOneSelector {0} 0 =
    [0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5,
      12, 13, 14, 18, 19, 20, 21, 22, 23, 15, 16, 17] := by
  decide

example : (clrsHamiltonianInstance twoEdgesOneSelector).PathAdjacent
      (selectedSourceVertexPath twoEdgesOneSelector {0} 0) := by
  exact selectedSourceVertexPath_pathAdjacent (by decide)

example : (clrsHamiltonianInstance twoEdgesOneSelector).Adj 24 0 := by
  simpa [twoEdgesOneSelector, selectorVertex, selectorBase, incidentVertex, globalWidgetVertex,
    widgetVertex, widgetVertexCount] using
    (adj_selector_incident_first
      (I := twoEdgesOneSelector) (u := 0) (selector := 0)
      (first := { occurrence := 0, rightSide := false })
      (rest := [{ occurrence := 1, rightSide := false }])
      (by decide) (by decide) (by decide))

example : (clrsHamiltonianInstance twoEdgesOneSelector).Adj 17 24 := by
  simpa [twoEdgesOneSelector, selectorVertex, selectorBase, incidentVertex, globalWidgetVertex,
    widgetVertex, widgetVertexCount] using
    (adj_incident_last_selector
      (I := twoEdgesOneSelector) (u := 0) (selector := 0)
      (first := { occurrence := 0, rightSide := false })
      (rest := [{ occurrence := 1, rightSide := false }])
      (by decide) (by decide) (by decide))

example : (clrsHamiltonianInstance oneEdgeTwoSelectors).Adj 12 13 := by
  simpa [oneEdgeTwoSelectors, selectorVertex, selectorBase, widgetVertexCount] using
    (adj_selector_selector (I := oneEdgeTwoSelectors)
      (first := 0) (second := 1) (by decide) (by decide) (by decide))

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
#print axioms selectedIncidenceChainPath_pathAdjacent_of_suffix
#print axioms selectedSourceVertexPath_pathAdjacent
#print axioms adj_selector_incident_first
#print axioms adj_incident_last_selector
#print axioms adj_selector_selector

end CLRS.Tests.Chapter34HamiltonianCycleReductionConstruction
