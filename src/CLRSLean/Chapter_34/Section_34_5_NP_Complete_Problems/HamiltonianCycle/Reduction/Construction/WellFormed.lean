import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Instance

/-!
# Well-formedness of the constructed Hamiltonian graph

Every generated edge is normalized and lies below the explicit target vertex
count.  The proof is split by the four edge families from `Edges.lean`.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem mem_allGlobalWidgetEdges_wellFormed
    {edgeCount selectorCount : Nat} {edge : Nat × Nat}
    (hedge : edge ∈ allGlobalWidgetEdges edgeCount) :
    edge.1 < edge.2 ∧ edge.2 < selectorBase edgeCount + selectorCount := by
  simp only [allGlobalWidgetEdges, List.mem_flatMap, List.mem_range] at hedge
  rcases hedge with ⟨occurrence, hoccurrence, hedge⟩
  simp only [globalWidgetEdges, List.mem_map] at hedge
  rcases hedge with ⟨localEdge, hlocalEdge, rfl⟩
  have hlocal := widgetInstance_wellFormed.2 localEdge hlocalEdge
  constructor
  · simp only [globalWidgetVertex]
    omega
  · have hbound := globalWidgetVertex_lt_selectorBase hoccurrence hlocal.2
    omega

theorem mem_allIncidenceChainEdges_wellFormed
    (I : CliqueInstance) {edge : Nat × Nat}
    (hedge : edge ∈ allIncidenceChainEdges I) :
    edge.1 < edge.2 ∧
      edge.2 < selectorBase I.edges.length + I.targetSize := by
  simp only [allIncidenceChainEdges, List.mem_flatMap, List.mem_range] at hedge
  rcases hedge with ⟨u, hu, hedge⟩
  rcases mem_incidenceChainEdges_of_pairwise
      (incidentOccurrences_pairwise I u) hedge with
    ⟨first, second, hfirst, hsecond, hoccurrence, rfl⟩
  have hvertices : incidentVertex first 5 < incidentVertex second 0 :=
    incidentVertex_lt_of_occurrence_lt hoccurrence (by omega) (by omega)
  have hfirstBound := incidentVertex_lt_selectorBase
    (position := 5) hfirst (by omega)
  have hsecondBound := incidentVertex_lt_selectorBase
    (position := 0) hsecond (by omega)
  constructor
  · exact normalizeUndirectedEdge_fst_lt_snd (Nat.ne_of_lt hvertices)
  · have := normalizeUndirectedEdge_snd_lt hfirstBound hsecondBound
    omega

theorem mem_allSelectorEndpointEdges_wellFormed
    (I : CliqueInstance) {edge : Nat × Nat}
    (hedge : edge ∈ allSelectorEndpointEdges I) :
    edge.1 < edge.2 ∧
      edge.2 < selectorBase I.edges.length + I.targetSize := by
  simp only [allSelectorEndpointEdges, List.mem_flatMap, List.mem_range] at hedge
  rcases hedge with ⟨u, hu, hedge⟩
  rcases mem_selectorEndpointEdgesFor hedge with
    ⟨ref, position, selector, href, hposition, hselector, rfl⟩
  have hincident := incidentVertex_lt_selectorBase href hposition
  have hselectorBound := selectorVertex_lt
    (edgeCount := I.edges.length) hselector
  have hincidentBound : incidentVertex ref position <
      selectorBase I.edges.length + I.targetSize := by
    omega
  have hlt : incidentVertex ref position <
      selectorVertex I.edges.length selector := by
    simp only [selectorVertex]
    omega
  constructor
  · exact normalizeUndirectedEdge_fst_lt_snd (Nat.ne_of_lt hlt)
  · exact normalizeUndirectedEdge_snd_lt hincidentBound hselectorBound

theorem mem_selectorCliqueEdges_wellFormed
    {edgeCount selectorCount : Nat} {edge : Nat × Nat}
    (hedge : edge ∈ selectorCliqueEdges edgeCount selectorCount) :
    edge.1 < edge.2 ∧
      edge.2 < selectorBase edgeCount + selectorCount := by
  rcases mem_selectorCliqueEdges_iff.mp hedge with
    ⟨first, second, hlt, hbound, rfl⟩
  constructor
  · simp [selectorVertex]
    omega
  · exact selectorVertex_lt hbound

theorem mem_clrsReductionEdges_wellFormed
    (I : CliqueInstance) {edge : Nat × Nat}
    (hedge : edge ∈ clrsReductionEdges I) :
    edge.1 < edge.2 ∧
      edge.2 < selectorBase I.edges.length + I.targetSize := by
  unfold clrsReductionEdges at hedge
  rcases List.mem_append.mp hedge with hedge | hedge
  · rcases List.mem_append.mp hedge with hedge | hedge
    · rcases List.mem_append.mp hedge with hedge | hedge
      · exact mem_allGlobalWidgetEdges_wellFormed hedge
      · exact mem_allIncidenceChainEdges_wellFormed I hedge
    · exact mem_allSelectorEndpointEdges_wellFormed I hedge
  · exact mem_selectorCliqueEdges_wellFormed hedge

theorem clrsHamiltonianInstance_wellFormed (I : VertexCoverInstance) :
    (clrsHamiltonianInstance I).WellFormed := by
  constructor
  · exact le_rfl
  · intro edge hedge
    exact mem_clrsReductionEdges_wellFormed I hedge

theorem vertexCoverToHamiltonianInstance_wellFormed
    (I : VertexCoverInstance) :
    (vertexCoverToHamiltonianInstance I).WellFormed := by
  simp only [vertexCoverToHamiltonianInstance]
  split
  · exact canonicalHamiltonianYesInstance_wellFormed
  · split
    · exact canonicalHamiltonianNoInstance_wellFormed
    · exact clrsHamiltonianInstance_wellFormed I

end CLRS.Chapter34.HamiltonianCycleReduction
