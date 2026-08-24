import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.LocalPaths

/-!
# Paths through one source vertex's incident gadgets

The CLRS construction orders all edge gadgets incident on a source vertex and
joins their corresponding six-vertex sides.  This file concatenates the local
traversals chosen by a source cover and proves that the result follows target
edges from the first incidence port to the last one.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Concatenate the cover-selected traversals for a list of incidences. -/
def selectedIncidenceChainPath
    (I : CliqueInstance) (cover : Finset Nat)
    (refs : List IncidentOccurrence) : List Nat :=
  refs.flatMap (selectedGlobalWidgetPath I cover)

/-- The complete target path represented by one selected source vertex. -/
def selectedSourceVertexPath
    (I : CliqueInstance) (cover : Finset Nat) (u : Nat) : List Nat :=
  selectedIncidenceChainPath I cover (incidentOccurrences I u)

theorem selectedIncidenceChainPath_head
    (I : CliqueInstance) (cover : Finset Nat)
    (first : IncidentOccurrence) (rest : List IncidentOccurrence) :
    (selectedIncidenceChainPath I cover (first :: rest)).head? =
      some (incidentVertex first 0) := by
  simp [selectedIncidenceChainPath, selectedGlobalWidgetPath_head]

theorem selectedIncidenceChainPath_getLast
    (I : CliqueInstance) (cover : Finset Nat)
    (first : IncidentOccurrence) (rest : List IncidentOccurrence) :
    (selectedIncidenceChainPath I cover (first :: rest)).getLast? =
      some (incidentVertex ((first :: rest).getLast (by simp)) 5) := by
  induction rest generalizing first with
  | nil =>
      simp [selectedIncidenceChainPath, selectedGlobalWidgetPath_getLast]
  | cons second rest ih =>
      simp only [selectedIncidenceChainPath, List.flatMap_cons]
      rw [List.getLast?_append_of_ne_nil]
      · simpa [selectedIncidenceChainPath] using ih second
      · change selectedIncidenceChainPath I cover (second :: rest) ≠ []
        intro hempty
        have hhead := selectedIncidenceChainPath_head I cover second rest
        rw [hempty] at hhead
        simp at hhead

/-- A connector generated for a consecutive suffix also occurs in the full
incidence-chain edge list. -/
theorem mem_incidenceChainEdges_of_cons_cons_suffix
    {first second : IncidentOccurrence} {rest refs : List IncidentOccurrence}
    (hsuffix : first :: second :: rest <:+ refs) :
    normalizeUndirectedEdge (incidentVertex first 5)
        (incidentVertex second 0) ∈ incidenceChainEdges refs := by
  rcases hsuffix with ⟨pre, rfl⟩
  induction pre with
  | nil => simp [incidenceChainEdges]
  | cons ref pre ih =>
      cases pre with
      | nil => simp [incidenceChainEdges]
      | cons next pre =>
          simp only [List.cons_append, incidenceChainEdges, List.mem_cons]
          exact Or.inr ih

/-- Successive incidence paths are joined by an edge of the constructed
target graph. -/
theorem adj_incident_chain_connector
    {I : CliqueInstance} {u : Nat}
    {first second : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hsuffix : first :: second :: rest <:+ incidentOccurrences I u) :
    (clrsHamiltonianInstance I).Adj
      (incidentVertex first 5) (incidentVertex second 0) := by
  have hpairwise : (first :: second :: rest).Pairwise
      (fun left right => left.occurrence < right.occurrence) :=
    (incidentOccurrences_pairwise I u).sublist hsuffix.sublist
  have hoccurrence : first.occurrence < second.occurrence :=
    (List.pairwise_cons.mp hpairwise).1 second (by simp)
  have hvertices : incidentVertex first 5 < incidentVertex second 0 :=
    incidentVertex_lt_of_occurrence_lt hoccurrence (by omega) (by omega)
  have hchain : normalizeUndirectedEdge (incidentVertex first 5)
      (incidentVertex second 0) ∈ allIncidenceChainEdges I := by
    simp only [allIncidenceChainEdges, List.mem_flatMap, List.mem_range]
    exact ⟨u, hu, mem_incidenceChainEdges_of_cons_cons_suffix hsuffix⟩
  have hchain' : (incidentVertex first 5, incidentVertex second 0) ∈
      allIncidenceChainEdges I := by
    simpa [normalizeUndirectedEdge, hvertices] using hchain
  apply CliqueInstance.adj_of_mem (I := clrsHamiltonianInstance I) hvertices
  simp [clrsHamiltonianInstance, clrsReductionEdges, hchain']

/-- Concatenating all chosen local traversals along one incidence suffix gives
a genuine path of the constructed graph. -/
theorem selectedIncidenceChainPath_pathAdjacent_of_suffix
    {I : CliqueInstance} {u : Nat} {cover : Finset Nat}
    {refs : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hsuffix : refs <:+ incidentOccurrences I u) :
    (clrsHamiltonianInstance I).PathAdjacent
      (selectedIncidenceChainPath I cover refs) := by
  rw [CliqueInstance.pathAdjacent_iff_isChain]
  induction refs using List.twoStepInduction with
  | nil => simp [selectedIncidenceChainPath]
  | singleton ref =>
      have href : ref ∈ incidentOccurrences I u := by
        exact hsuffix.subset (by simp)
      simpa [selectedIncidenceChainPath] using
        (CliqueInstance.pathAdjacent_iff_isChain _ _).1
          (selectedGlobalWidgetPath_pathAdjacent href)
  | cons_cons first second rest ihRest ihTail =>
      simp only [selectedIncidenceChainPath, List.flatMap_cons]
      apply List.IsChain.append
      · have hfirst : first ∈ incidentOccurrences I u := by
          exact hsuffix.subset (by simp)
        exact (CliqueInstance.pathAdjacent_iff_isChain _ _).1
          (selectedGlobalWidgetPath_pathAdjacent hfirst)
      · apply ihTail second
        exact List.IsSuffix.trans (by simp) hsuffix
      · intro x hx y hy
        rw [selectedGlobalWidgetPath_getLast] at hx
        change y ∈ (selectedIncidenceChainPath I cover (second :: rest)).head? at hy
        rw [selectedIncidenceChainPath_head] at hy
        simp only [Option.mem_some_iff] at hx hy
        subst x
        subst y
        exact adj_incident_chain_connector hu hsuffix

theorem selectedSourceVertexPath_pathAdjacent
    {I : CliqueInstance} {cover : Finset Nat} {u : Nat}
    (hu : u < I.vertexCount) :
    (clrsHamiltonianInstance I).PathAdjacent
      (selectedSourceVertexPath I cover u) := by
  exact selectedIncidenceChainPath_pathAdjacent_of_suffix hu (by simp)

end CLRS.Chapter34.HamiltonianCycleReduction
