import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CoreNeighbors

/-!
# Adjacency inside one global gadget block

If both endpoints belong to the same occurrence block, incidence-chain and
selector edge families cannot contribute the adjacency.  Thus global
adjacency restricts exactly to the finite local gadget adjacency relation.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
    {occurrence localVertex position : Nat} {ref : IncidentOccurrence}
    (hlocal : localVertex < widgetVertexCount)
    (hposition : position < 6)
    (heq : globalWidgetVertex occurrence localVertex =
      incidentVertex ref position) :
    occurrence = ref.occurrence := by
  apply (globalWidgetVertex_injective_of_local_lt hlocal
    (widgetVertex_lt ref.rightSide hposition) heq).1

theorem globalWidgetVertex_ne_selectorVertex_of_lt
    {occurrence localVertex edgeCount selector : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hlocal : localVertex < widgetVertexCount) :
    globalWidgetVertex occurrence localVertex ≠
      selectorVertex edgeCount selector := by
  have hlt := globalWidgetVertex_lt_selectorBase hoccurrence hlocal
  simp only [selectorVertex]
  omega

theorem adj_same_globalWidgetOccurrence_iff
    {I : CliqueInstance} {occurrence firstLocal secondLocal : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hfirstLocal : firstLocal < widgetVertexCount)
    (hsecondLocal : secondLocal < widgetVertexCount) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence firstLocal)
        (globalWidgetVertex occurrence secondLocal) ↔
      widgetInstance.Adj firstLocal secondLocal := by
  constructor
  · intro hadj
    rcases endpoint_of_adj hadj with ⟨edge, hedge, hends⟩
    change edge ∈ clrsReductionEdges I at hedge
    unfold clrsReductionEdges at hedge
    rcases List.mem_append.mp hedge with hedge | hedgeClique
    · rcases List.mem_append.mp hedge with hedge | hedgeSelector
      · rcases List.mem_append.mp hedge with hedgeWidget | hedgeChain
        · rcases (mem_allGlobalWidgetEdges_iff).mp hedgeWidget with
            ⟨otherOccurrence, _, localEdge, hlocalEdge, rfl⟩
          have hlocalProperties := widgetInstance_wellFormed.2 _ hlocalEdge
          have hlocalFirst : localEdge.1 < widgetVertexCount := by
            change localEdge.1 < widgetInstance.vertexCount
            omega
          have hlocalSecond : localEdge.2 < widgetVertexCount :=
            hlocalProperties.2
          rcases hends with hends | hends
          · have hfirst := globalWidgetVertex_injective_of_local_lt
              hfirstLocal hlocalFirst hends.1
            have hsecond := globalWidgetVertex_injective_of_local_lt
              hsecondLocal hlocalSecond hends.2
            rw [hfirst.2, hsecond.2]
            exact CliqueInstance.adj_of_mem widgetInstance
              hlocalProperties.1 hlocalEdge
          · have hfirst := globalWidgetVertex_injective_of_local_lt
              hfirstLocal hlocalSecond hends.1
            have hsecond := globalWidgetVertex_injective_of_local_lt
              hsecondLocal hlocalFirst hends.2
            rw [hfirst.2, hsecond.2]
            exact (widgetInstance.adj_comm _ _).2
              (CliqueInstance.adj_of_mem widgetInstance
                hlocalProperties.1 hlocalEdge)
        · rcases mem_allIncidenceChainEdges_shape hedgeChain with
            ⟨u, first, second, _, _, _, hlt, rfl⟩
          simp only [normalizeUndirectedEdge] at hends
          split at hends <;> rcases hends with hends | hends
          · have hone := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hfirstLocal (by omega) hends.1
            have htwo := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hsecondLocal (by omega) hends.2
            omega
          · have hone := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hfirstLocal (by omega) hends.1
            have htwo := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hsecondLocal (by omega) hends.2
            omega
          · have hone := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hfirstLocal (by omega) hends.1
            have htwo := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hsecondLocal (by omega) hends.2
            omega
          · have hone := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hfirstLocal (by omega) hends.1
            have htwo := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
              hsecondLocal (by omega) hends.2
            omega
      · rcases mem_allSelectorEndpointEdges_shape hedgeSelector with
          ⟨u, ref, position, selector, _, _, hposition, _, rfl⟩
        have hneFirst := globalWidgetVertex_ne_selectorVertex_of_lt
          hoccurrence hfirstLocal (selector := selector)
        have hneSecond := globalWidgetVertex_ne_selectorVertex_of_lt
          hoccurrence hsecondLocal (selector := selector)
        simp only [normalizeUndirectedEdge] at hends
        split at hends <;> rcases hends with hends | hends <;> aesop
    · rcases mem_selectorCliqueEdges_iff.mp hedgeClique with
        ⟨first, second, _, _, rfl⟩
      have hneFirstLeft := globalWidgetVertex_ne_selectorVertex_of_lt
        hoccurrence hfirstLocal (selector := first)
      have hneFirstRight := globalWidgetVertex_ne_selectorVertex_of_lt
        hoccurrence hfirstLocal (selector := second)
      rcases hends with hends | hends <;> aesop
  · exact adj_globalWidgetVertex_of_widgetAdj I hoccurrence

end CLRS.Chapter34.HamiltonianCycleReduction
