import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction

/-!
# Local paths induced by a source vertex cover

For a selected source vertex, each incident edge occurrence contributes either
its six-vertex side (when both endpoints are selected) or the twelve-vertex
full traversal (when this is the only selected endpoint).  This file proves
that every such mapped traversal is a genuine path in the constructed graph.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Total source-edge lookup used by the executable certificate constructor. -/
def sourceEdgeForOccurrence (I : CliqueInstance) (ref : IncidentOccurrence) :
    Nat × Nat :=
  (I.edges[ref.occurrence]?).getD (0, 0)

/-- The endpoint opposite the source vertex represented by an incident side. -/
def otherEndpoint (I : CliqueInstance) (ref : IncidentOccurrence) : Nat :=
  if ref.rightSide then
    (sourceEdgeForOccurrence I ref).1
  else
    (sourceEdgeForOccurrence I ref).2

/-- Six-vertex traversal on the side represented by an incidence. -/
def widgetSidePath (ref : IncidentOccurrence) : List Nat :=
  if ref.rightSide then widgetRightPath else widgetLeftPath

/-- Twelve-vertex traversal whose external ports lie on the represented side. -/
def widgetFullPath (ref : IncidentOccurrence) : List Nat :=
  if ref.rightSide then widgetRightFullPath else widgetLeftFullPath

/-- Local traversal selected by a proposed source cover. -/
def selectedWidgetPath
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    List Nat :=
  if otherEndpoint I ref ∈ cover then
    widgetSidePath ref
  else
    widgetFullPath ref

/-- Move a local gadget path into its occurrence block. -/
def mapWidgetPath (ref : IncidentOccurrence) (path : List Nat) : List Nat :=
  path.map (globalWidgetVertex ref.occurrence)

/-- Globally numbered traversal chosen by a proposed source cover. -/
def selectedGlobalWidgetPath
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    List Nat :=
  mapWidgetPath ref (selectedWidgetPath I cover ref)

theorem sourceEdgeForOccurrence_eq_getElem
    {I : CliqueInstance} {ref : IncidentOccurrence}
    (hoccurrence : ref.occurrence < I.edges.length) :
    sourceEdgeForOccurrence I ref =
      I.edges.get ⟨ref.occurrence, hoccurrence⟩ := by
  simp [sourceEdgeForOccurrence, List.getElem?_eq_getElem hoccurrence]

theorem otherEndpoint_eq_of_left
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (_href : ref ∈ incidentOccurrences I u) (hside : ref.rightSide = false) :
    otherEndpoint I ref = (sourceEdgeForOccurrence I ref).2 := by
  simp [otherEndpoint, hside]

theorem otherEndpoint_eq_of_right
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (_href : ref ∈ incidentOccurrences I u) (hside : ref.rightSide = true) :
    otherEndpoint I ref = (sourceEdgeForOccurrence I ref).1 := by
  simp [otherEndpoint, hside]

theorem widgetSidePath_isWidgetPath (ref : IncidentOccurrence) :
    IsWidgetPath (widgetSidePath ref) := by
  cases ref with
  | mk occurrence rightSide =>
      cases rightSide
      · simpa [widgetSidePath] using widgetLeftPath_isWidgetPath
      · simpa [widgetSidePath] using widgetRightPath_isWidgetPath

theorem widgetFullPath_isWidgetPath (ref : IncidentOccurrence) :
    IsWidgetPath (widgetFullPath ref) := by
  cases ref with
  | mk occurrence rightSide =>
      cases rightSide
      · simpa [widgetFullPath] using widgetLeftFullPath_isWidgetPath
      · simpa [widgetFullPath] using widgetRightFullPath_isWidgetPath

theorem selectedWidgetPath_isWidgetPath
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    IsWidgetPath (selectedWidgetPath I cover ref) := by
  simp only [selectedWidgetPath]
  split
  · exact widgetSidePath_isWidgetPath ref
  · exact widgetFullPath_isWidgetPath ref

theorem selectedWidgetPath_head
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    (selectedWidgetPath I cover ref).head? = some (widgetVertex ref.rightSide 0) := by
  cases ref with
  | mk occurrence rightSide =>
      cases rightSide
      · by_cases hcover :
            otherEndpoint I { occurrence := occurrence, rightSide := false } ∈ cover <;>
          simp [selectedWidgetPath, hcover, widgetSidePath, widgetFullPath,
            widgetLeftPath, widgetLeftFullPath, widgetVertex]
      · by_cases hcover :
            otherEndpoint I { occurrence := occurrence, rightSide := true } ∈ cover <;>
          simp [selectedWidgetPath, hcover, widgetSidePath, widgetFullPath,
            widgetRightPath, widgetRightFullPath, widgetVertex]

theorem selectedWidgetPath_getLast
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    (selectedWidgetPath I cover ref).getLast? = some (widgetVertex ref.rightSide 5) := by
  cases ref with
  | mk occurrence rightSide =>
      cases rightSide
      · by_cases hcover :
            otherEndpoint I { occurrence := occurrence, rightSide := false } ∈ cover <;>
          simp [selectedWidgetPath, hcover, widgetSidePath, widgetFullPath,
            widgetLeftPath, widgetLeftFullPath, widgetVertex]
      · by_cases hcover :
            otherEndpoint I { occurrence := occurrence, rightSide := true } ∈ cover <;>
          simp [selectedWidgetPath, hcover, widgetSidePath, widgetFullPath,
            widgetRightPath, widgetRightFullPath, widgetVertex]

theorem selectedGlobalWidgetPath_head
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    (selectedGlobalWidgetPath I cover ref).head? =
      some (incidentVertex ref 0) := by
  simp [selectedGlobalWidgetPath, mapWidgetPath, incidentVertex,
    selectedWidgetPath_head]

theorem selectedGlobalWidgetPath_getLast
    (I : CliqueInstance) (cover : Finset Nat) (ref : IncidentOccurrence) :
    (selectedGlobalWidgetPath I cover ref).getLast? =
      some (incidentVertex ref 5) := by
  simp [selectedGlobalWidgetPath, mapWidgetPath, incidentVertex,
    selectedWidgetPath_getLast]

theorem mem_allGlobalWidgetEdges_of_mem
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {edge : Nat × Nat} (hedge : edge ∈ widgetEdges) :
    (globalWidgetVertex occurrence edge.1,
      globalWidgetVertex occurrence edge.2) ∈ clrsReductionEdges I := by
  have hglobal :
      (globalWidgetVertex occurrence edge.1,
        globalWidgetVertex occurrence edge.2) ∈
          allGlobalWidgetEdges I.edges.length := by
    simp only [allGlobalWidgetEdges, List.mem_flatMap, List.mem_range]
    refine ⟨occurrence, hoccurrence, ?_⟩
    simp only [globalWidgetEdges, List.mem_map]
    exact ⟨edge, hedge, rfl⟩
  simp [clrsReductionEdges, hglobal]

theorem adj_globalWidgetVertex_of_adj
    (I : CliqueInstance) {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {u v : Nat} (hadj : widgetInstance.Adj u v) :
    (clrsHamiltonianInstance I).Adj
      (globalWidgetVertex occurrence u)
      (globalWidgetVertex occurrence v) := by
  rw [CliqueInstance.adj_iff] at hadj
  rcases hadj with ⟨huv, hedge⟩ | ⟨hvu, hedge⟩
  · apply CliqueInstance.adj_of_mem
    · simp [globalWidgetVertex]
      omega
    · exact mem_allGlobalWidgetEdges_of_mem hoccurrence hedge
  · rw [CliqueInstance.adj_comm]
    apply CliqueInstance.adj_of_mem
    · simp [globalWidgetVertex]
      omega
    · exact mem_allGlobalWidgetEdges_of_mem hoccurrence hedge

theorem pathAdjacent_mapWidgetPath
    (I : CliqueInstance) {ref : IncidentOccurrence}
    (hoccurrence : ref.occurrence < I.edges.length)
    {path : List Nat} (hpath : IsWidgetPath path) :
    (clrsHamiltonianInstance I).PathAdjacent (mapWidgetPath ref path) := by
  rw [CliqueInstance.pathAdjacent_iff_isChain]
  rw [mapWidgetPath, List.isChain_map]
  have hlocal :=
    (widgetInstance.pathAdjacent_iff_isChain path).1 hpath.2.2
  exact hlocal.imp fun _ _ hadj =>
    adj_globalWidgetVertex_of_adj I hoccurrence hadj

theorem selectedGlobalWidgetPath_pathAdjacent
    {I : CliqueInstance} {u : Nat} {cover : Finset Nat}
    {ref : IncidentOccurrence} (href : ref ∈ incidentOccurrences I u) :
    (clrsHamiltonianInstance I).PathAdjacent
      (selectedGlobalWidgetPath I cover ref) := by
  apply pathAdjacent_mapWidgetPath I
  · exact occurrence_lt_of_mem_incidentOccurrences href
  · exact selectedWidgetPath_isWidgetPath I cover ref

end CLRS.Chapter34.HamiltonianCycleReduction
