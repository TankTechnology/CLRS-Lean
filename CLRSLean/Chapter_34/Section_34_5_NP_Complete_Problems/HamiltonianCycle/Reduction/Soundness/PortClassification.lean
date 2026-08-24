import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.SelectedPorts

/-!
# Classifying external port links

An external Hamiltonian-cycle link at position `0` either comes from a
strictly earlier occurrence in the same source-vertex incidence chain or from
a selector.  Dually, an external link at position `5` goes to a strictly
later occurrence or to a selector.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem incidentVertex_injective
    {first second : IncidentOccurrence} {firstPosition secondPosition : Nat}
    (hfirstPosition : firstPosition < 6)
    (hsecondPosition : secondPosition < 6)
    (heq : incidentVertex first firstPosition =
      incidentVertex second secondPosition) :
    first = second ∧ firstPosition = secondPosition := by
  cases first with
  | mk firstOccurrence firstSide =>
      cases second with
      | mk secondOccurrence secondSide =>
          cases firstSide <;> cases secondSide <;>
            simp [incidentVertex, globalWidgetVertex, widgetVertex,
              widgetVertexCount] at heq ⊢ <;> omega

theorem source_eq_of_mem_incidentOccurrences
    {I : CliqueInstance} {firstSource secondSource : Nat}
    {ref : IncidentOccurrence}
    (hfirst : ref ∈ incidentOccurrences I firstSource)
    (hsecond : ref ∈ incidentOccurrences I secondSource) :
    firstSource = secondSource := by
  obtain ⟨_, hfirstSide⟩ := endpoints_of_mem_incidentOccurrences hfirst
  obtain ⟨_, hsecondSide⟩ := endpoints_of_mem_incidentOccurrences hsecond
  rcases hfirstSide with hfirstSide | hfirstSide <;>
    rcases hsecondSide with hsecondSide | hsecondSide
  all_goals simp_all

theorem incidentVertex_ne_selectorVertex
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    {position selector : Nat} (hposition : position < 6) :
    incidentVertex ref position ≠
      selectorVertex I.edges.length selector := by
  have hlt := incidentVertex_lt_selectorBase href hposition
  simp only [selectorVertex, selectorBase] at hlt ⊢
  omega

theorem external_cycle_link_zero_shape
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    (hexternal : CyclePortHasExternalLink vertices ref 0) :
    (∃ previous,
        previous ∈ incidentOccurrences I u ∧
        previous.occurrence < ref.occurrence ∧
        CycleLinked vertices (incidentVertex ref 0)
          (incidentVertex previous 5)) ∨
      ∃ selector, selector < I.targetSize ∧
        CycleLinked vertices (incidentVertex ref 0)
          (selectorVertex I.edges.length selector) := by
  rcases hexternal with ⟨vertex, hlinked, houtside⟩
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hadj := adj_of_cycleLinked hnodup hcycleAdjacent hlinked
  rcases endpoint_of_adj hadj with ⟨edge, hedge, hends⟩
  change edge ∈ clrsReductionEdges I at hedge
  unfold clrsReductionEdges at hedge
  rcases List.mem_append.mp hedge with hedge | hedgeClique
  · rcases List.mem_append.mp hedge with hedge | hedgeSelector
    · rcases List.mem_append.mp hedge with hedgeWidget | hedgeChain
      · rcases (mem_allGlobalWidgetEdges_iff).mp hedgeWidget with
          ⟨occurrence, _, localEdge, hlocalEdge, rfl⟩
        have hlocalProperties := widgetInstance_wellFormed.2 _ hlocalEdge
        have hfirstLocal : localEdge.1 < widgetVertexCount := by
          change localEdge.1 < widgetInstance.vertexCount
          omega
        have hsecondLocal : localEdge.2 < widgetVertexCount :=
          hlocalProperties.2
        apply (houtside ?_).elim
        rcases hends with hends | hends
        · have hoccurrence :=
              occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
                hfirstLocal (by omega) hends.1.symm
          exact ⟨localEdge.2, hsecondLocal, by simpa [hoccurrence] using hends.2⟩
        · have hoccurrence :=
              occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
                hsecondLocal (by omega) hends.1.symm
          exact ⟨localEdge.1, hfirstLocal, by simpa [hoccurrence] using hends.2⟩
      · rcases mem_allIncidenceChainEdges_shape hedgeChain with
          ⟨otherSource, first, second, _, hfirst, hsecond, hlt, rfl⟩
        have hvertices := incidentVertex_lt_of_occurrence_lt hlt
          (show 5 < 6 by decide) (show 0 < 6 by decide)
        simp only [normalizeUndirectedEdge, if_pos hvertices] at hends
        rcases hends with hends | hends
        · have hident := incidentVertex_injective
              (show 0 < 6 by decide) (show 5 < 6 by decide) hends.1
          omega
        · have hident := incidentVertex_injective
              (show 0 < 6 by decide) (show 0 < 6 by decide) hends.1
          have hsource := source_eq_of_mem_incidentOccurrences href
            (hident.1 ▸ hsecond)
          left
          refine ⟨first, hsource ▸ hfirst, ?_, ?_⟩
          · simpa [hident.1] using hlt
          · simpa [hends.2] using hlinked
    · rcases mem_allSelectorEndpointEdges_shape hedgeSelector with
        ⟨otherSource, otherRef, position, selector, _, hotherRef,
          hposition, hselector, rfl⟩
      have hpositionLt : position < 6 := by rcases hposition with rfl | rfl <;> decide
      have hportLt := incidentVertex_lt_selectorBase hotherRef hpositionLt
      have hvertices : incidentVertex otherRef position <
          selectorVertex I.edges.length selector := by
        simp only [selectorVertex]
        omega
      simp only [normalizeUndirectedEdge, if_pos hvertices] at hends
      rcases hends with hends | hends
      · have hident := incidentVertex_injective
            (show 0 < 6 by decide) hpositionLt hends.1
        right
        refine ⟨selector, hselector, ?_⟩
        simpa [hends.2] using hlinked
      · exact (incidentVertex_ne_selectorVertex href
            (show 0 < 6 by decide) hends.1).elim
  · rcases mem_selectorCliqueEdges_iff.mp hedgeClique with
      ⟨first, second, _, _, rfl⟩
    rcases hends with hends | hends
    · exact (incidentVertex_ne_selectorVertex href
          (show 0 < 6 by decide) hends.1).elim
    · exact (incidentVertex_ne_selectorVertex href
          (show 0 < 6 by decide) hends.1).elim

theorem external_cycle_link_five_shape
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    (hexternal : CyclePortHasExternalLink vertices ref 5) :
    (∃ next,
        next ∈ incidentOccurrences I u ∧
        ref.occurrence < next.occurrence ∧
        CycleLinked vertices (incidentVertex ref 5)
          (incidentVertex next 0)) ∨
      ∃ selector, selector < I.targetSize ∧
        CycleLinked vertices (incidentVertex ref 5)
          (selectorVertex I.edges.length selector) := by
  rcases hexternal with ⟨vertex, hlinked, houtside⟩
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hadj := adj_of_cycleLinked hnodup hcycleAdjacent hlinked
  rcases endpoint_of_adj hadj with ⟨edge, hedge, hends⟩
  change edge ∈ clrsReductionEdges I at hedge
  unfold clrsReductionEdges at hedge
  rcases List.mem_append.mp hedge with hedge | hedgeClique
  · rcases List.mem_append.mp hedge with hedge | hedgeSelector
    · rcases List.mem_append.mp hedge with hedgeWidget | hedgeChain
      · rcases (mem_allGlobalWidgetEdges_iff).mp hedgeWidget with
          ⟨occurrence, _, localEdge, hlocalEdge, rfl⟩
        have hlocalProperties := widgetInstance_wellFormed.2 _ hlocalEdge
        have hfirstLocal : localEdge.1 < widgetVertexCount := by
          change localEdge.1 < widgetInstance.vertexCount
          omega
        have hsecondLocal : localEdge.2 < widgetVertexCount :=
          hlocalProperties.2
        apply (houtside ?_).elim
        rcases hends with hends | hends
        · have hoccurrence :=
              occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
                hfirstLocal (by omega) hends.1.symm
          exact ⟨localEdge.2, hsecondLocal, by simpa [hoccurrence] using hends.2⟩
        · have hoccurrence :=
              occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
                hsecondLocal (by omega) hends.1.symm
          exact ⟨localEdge.1, hfirstLocal, by simpa [hoccurrence] using hends.2⟩
      · rcases mem_allIncidenceChainEdges_shape hedgeChain with
          ⟨otherSource, first, second, _, hfirst, hsecond, hlt, rfl⟩
        have hvertices := incidentVertex_lt_of_occurrence_lt hlt
          (show 5 < 6 by decide) (show 0 < 6 by decide)
        simp only [normalizeUndirectedEdge, if_pos hvertices] at hends
        rcases hends with hends | hends
        · have hident := incidentVertex_injective
              (show 5 < 6 by decide) (show 5 < 6 by decide) hends.1
          have hsource := source_eq_of_mem_incidentOccurrences href
            (hident.1 ▸ hfirst)
          left
          refine ⟨second, hsource ▸ hsecond, ?_, ?_⟩
          · simpa [hident.1] using hlt
          · simpa [hends.2] using hlinked
        · have hident := incidentVertex_injective
              (show 5 < 6 by decide) (show 0 < 6 by decide) hends.1
          omega
    · rcases mem_allSelectorEndpointEdges_shape hedgeSelector with
        ⟨otherSource, otherRef, position, selector, _, hotherRef,
          hposition, hselector, rfl⟩
      have hpositionLt : position < 6 := by rcases hposition with rfl | rfl <;> decide
      have hportLt := incidentVertex_lt_selectorBase hotherRef hpositionLt
      have hvertices : incidentVertex otherRef position <
          selectorVertex I.edges.length selector := by
        simp only [selectorVertex]
        omega
      simp only [normalizeUndirectedEdge, if_pos hvertices] at hends
      rcases hends with hends | hends
      · have hident := incidentVertex_injective
            (show 5 < 6 by decide) hpositionLt hends.1
        right
        refine ⟨selector, hselector, ?_⟩
        simpa [hends.2] using hlinked
      · exact (incidentVertex_ne_selectorVertex href
            (show 5 < 6 by decide) hends.1).elim
  · rcases mem_selectorCliqueEdges_iff.mp hedgeClique with
      ⟨first, second, _, _, rfl⟩
    rcases hends with hends | hends
    · exact (incidentVertex_ne_selectorVertex href
          (show 5 < 6 by decide) hends.1).elim
    · exact (incidentVertex_ne_selectorVertex href
          (show 5 < 6 by decide) hends.1).elim

end CLRS.Chapter34.HamiltonianCycleReduction
