import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.ChainPaths

/-!
# Selector edges used by the completeness certificate

Every selector is connected to both endpoints of every nonempty source-vertex
incidence chain, and all distinct selectors are mutually adjacent.  These
introduction lemmas hide normalized-edge bookkeeping from the later cycle
builder.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem mem_selectorEndpointEdgesFor_first
    {edgeCount selectorCount selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hselector : selector < selectorCount) :
    normalizeUndirectedEdge (incidentVertex first 0)
        (selectorVertex edgeCount selector) ∈
      selectorEndpointEdgesFor edgeCount selectorCount (first :: rest) := by
  simp only [selectorEndpointEdgesFor, List.mem_flatMap, List.mem_range]
  exact ⟨selector, hselector, by simp⟩

theorem mem_selectorEndpointEdgesFor_last
    {edgeCount selectorCount selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hselector : selector < selectorCount) :
    normalizeUndirectedEdge
        (incidentVertex ((first :: rest).getLast (by simp)) 5)
        (selectorVertex edgeCount selector) ∈
      selectorEndpointEdgesFor edgeCount selectorCount (first :: rest) := by
  simp only [selectorEndpointEdgesFor, List.mem_flatMap, List.mem_range]
  exact ⟨selector, hselector, by simp⟩

theorem mem_allSelectorEndpointEdges_of_first
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    normalizeUndirectedEdge (incidentVertex first 0)
        (selectorVertex I.edges.length selector) ∈
      allSelectorEndpointEdges I := by
  simp only [allSelectorEndpointEdges, List.mem_flatMap, List.mem_range]
  refine ⟨u, hu, ?_⟩
  rw [hrefs]
  exact mem_selectorEndpointEdgesFor_first hselector

theorem mem_allSelectorEndpointEdges_of_last
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    normalizeUndirectedEdge
        (incidentVertex ((first :: rest).getLast (by simp)) 5)
        (selectorVertex I.edges.length selector) ∈
      allSelectorEndpointEdges I := by
  simp only [allSelectorEndpointEdges, List.mem_flatMap, List.mem_range]
  refine ⟨u, hu, ?_⟩
  rw [hrefs]
  exact mem_selectorEndpointEdgesFor_last hselector

theorem adj_incident_first_selector
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    (clrsHamiltonianInstance I).Adj (incidentVertex first 0)
      (selectorVertex I.edges.length selector) := by
  have hfirst : first ∈ incidentOccurrences I u := by
    rw [hrefs]
    simp
  have hincident := incidentVertex_lt_selectorBase
    (position := 0) hfirst (by omega)
  have hlt : incidentVertex first 0 <
      selectorVertex I.edges.length selector := by
    simp only [selectorVertex]
    omega
  have hedge := mem_allSelectorEndpointEdges_of_first hu hrefs hselector
  have hedge' : (incidentVertex first 0,
      selectorVertex I.edges.length selector) ∈
      allSelectorEndpointEdges I := by
    simpa [normalizeUndirectedEdge, hlt] using hedge
  apply CliqueInstance.adj_of_mem (I := clrsHamiltonianInstance I) hlt
  simp [clrsHamiltonianInstance, clrsReductionEdges, hedge']

theorem adj_selector_incident_first
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    (clrsHamiltonianInstance I).Adj
      (selectorVertex I.edges.length selector) (incidentVertex first 0) := by
  rw [CliqueInstance.adj_comm]
  exact adj_incident_first_selector hu hrefs hselector

theorem adj_incident_last_selector
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    (clrsHamiltonianInstance I).Adj
      (incidentVertex ((first :: rest).getLast (by simp)) 5)
      (selectorVertex I.edges.length selector) := by
  have hlast : (first :: rest).getLast (by simp) ∈
      incidentOccurrences I u := by
    rw [hrefs]
    exact List.getLast_mem _
  have hincident := incidentVertex_lt_selectorBase
    (position := 5) hlast (by omega)
  have hlt : incidentVertex ((first :: rest).getLast (by simp)) 5 <
      selectorVertex I.edges.length selector := by
    simp only [selectorVertex]
    omega
  have hedge := mem_allSelectorEndpointEdges_of_last hu hrefs hselector
  have hedge' :
      (incidentVertex ((first :: rest).getLast (by simp)) 5,
        selectorVertex I.edges.length selector) ∈
        allSelectorEndpointEdges I := by
    simpa [normalizeUndirectedEdge, hlt] using hedge
  apply CliqueInstance.adj_of_mem (I := clrsHamiltonianInstance I) hlt
  simp [clrsHamiltonianInstance, clrsReductionEdges, hedge']

theorem adj_selector_incident_last
    {I : CliqueInstance} {u selector : Nat}
    {first : IncidentOccurrence} {rest : List IncidentOccurrence}
    (hu : u < I.vertexCount)
    (hrefs : incidentOccurrences I u = first :: rest)
    (hselector : selector < I.targetSize) :
    (clrsHamiltonianInstance I).Adj
      (selectorVertex I.edges.length selector)
      (incidentVertex ((first :: rest).getLast (by simp)) 5) := by
  rw [CliqueInstance.adj_comm]
  exact adj_incident_last_selector hu hrefs hselector

theorem adj_selector_selector
    {I : CliqueInstance} {first second : Nat}
    (hfirst : first < I.targetSize) (hsecond : second < I.targetSize)
    (hne : first ≠ second) :
    (clrsHamiltonianInstance I).Adj
      (selectorVertex I.edges.length first)
      (selectorVertex I.edges.length second) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hedge :
        (selectorVertex I.edges.length first,
          selectorVertex I.edges.length second) ∈
          selectorCliqueEdges I.edges.length I.targetSize :=
      mem_selectorCliqueEdges_iff.mpr ⟨first, second, hlt, hsecond, rfl⟩
    have hvertices : selectorVertex I.edges.length first <
        selectorVertex I.edges.length second := by
      simp [selectorVertex]
      omega
    apply CliqueInstance.adj_of_mem
      (I := clrsHamiltonianInstance I) hvertices
    simp [clrsHamiltonianInstance, clrsReductionEdges, hedge]
  · rw [CliqueInstance.adj_comm]
    have hedge :
        (selectorVertex I.edges.length second,
          selectorVertex I.edges.length first) ∈
          selectorCliqueEdges I.edges.length I.targetSize :=
      mem_selectorCliqueEdges_iff.mpr ⟨second, first, hgt, hfirst, rfl⟩
    have hvertices : selectorVertex I.edges.length second <
        selectorVertex I.edges.length first := by
      simp [selectorVertex]
      omega
    apply CliqueInstance.adj_of_mem
      (I := clrsHamiltonianInstance I) hvertices
    simp [clrsHamiltonianInstance, clrsReductionEdges, hedge]

end CLRS.Chapter34.HamiltonianCycleReduction
