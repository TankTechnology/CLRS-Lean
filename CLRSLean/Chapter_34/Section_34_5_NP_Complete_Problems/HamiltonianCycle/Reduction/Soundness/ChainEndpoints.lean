import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.PortClassification

/-!
# Reaching selectors along selected incidence chains

External port links strictly decrease occurrence indices on the left and
strictly increase them on the right.  Well-founded recursion therefore shows
that both directions eventually reach selector vertices.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem incidentVertex_not_in_earlier_occurrence
    {first second : IncidentOccurrence} {position : Nat}
    (hlt : first.occurrence < second.occurrence)
    (hposition : position < 6) :
    ¬IsOccurrenceWidgetVertex first.occurrence
      (incidentVertex second position) := by
  rintro ⟨localVertex, hlocal, heq⟩
  have hoccurrence := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
    hlocal hposition heq.symm
  omega

theorem incidentVertex_not_in_later_occurrence
    {first second : IncidentOccurrence} {position : Nat}
    (hlt : first.occurrence < second.occurrence)
    (hposition : position < 6) :
    ¬IsOccurrenceWidgetVertex second.occurrence
      (incidentVertex first position) := by
  rintro ⟨localVertex, hlocal, heq⟩
  have hoccurrence := occurrence_eq_of_globalWidgetVertex_eq_incidentVertex
    hlocal hposition heq.symm
  omega

theorem exists_left_selector_endpoint
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    (hselected : CycleUsesIncidentSide vertices ref) :
    ∃ endpoint,
      endpoint ∈ incidentOccurrences I u ∧
      CycleUsesIncidentSide vertices endpoint ∧
      endpoint.occurrence ≤ ref.occurrence ∧
      ∃ selector, selector < I.targetSize ∧
        CycleLinked vertices (incidentVertex endpoint 0)
          (selectorVertex I.edges.length selector) := by
  have hrefLt := occurrence_lt_of_mem_incidentOccurrences href
  have hexternal :=
    (cycleUsesIncidentSide_has_external_links hcycle hrefLt hselected).1
  rcases external_cycle_link_zero_shape hcycle href hexternal with
    hprevious | hselector
  · rcases hprevious with ⟨previous, hpreviousMem, hlt, hlinked⟩
    rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
    have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
        vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
    have hpreviousExternal : CyclePortHasExternalLink vertices previous 5 :=
      ⟨incidentVertex ref 0, cycleLinked_symm hnodup hlinked,
        incidentVertex_not_in_earlier_occurrence hlt (by decide)⟩
    have hpreviousSelected :=
      cyclePortFiveExternalLink_implies_usesIncidentSide hfull htarget
        (occurrence_lt_of_mem_incidentOccurrences hpreviousMem)
        hpreviousExternal
    obtain ⟨endpoint, hendpointMem, hendpointSelected, hendpointLe,
        selector, hselectorLt, hselectorLinked⟩ :=
      exists_left_selector_endpoint hfull htarget hpreviousMem
        hpreviousSelected
    exact ⟨endpoint, hendpointMem, hendpointSelected,
      Nat.le_trans hendpointLe (Nat.le_of_lt hlt), selector,
      hselectorLt, hselectorLinked⟩
  · rcases hselector with ⟨selector, hselectorLt, hselectorLinked⟩
    exact ⟨ref, href, hselected, Nat.le_refl _, selector,
      hselectorLt, hselectorLinked⟩
termination_by ref.occurrence

theorem exists_right_selector_endpoint
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    (hselected : CycleUsesIncidentSide vertices ref) :
    ∃ endpoint,
      endpoint ∈ incidentOccurrences I u ∧
      CycleUsesIncidentSide vertices endpoint ∧
      ref.occurrence ≤ endpoint.occurrence ∧
      ∃ selector, selector < I.targetSize ∧
        CycleLinked vertices (incidentVertex endpoint 5)
          (selectorVertex I.edges.length selector) := by
  have hrefLt := occurrence_lt_of_mem_incidentOccurrences href
  have hexternal :=
    (cycleUsesIncidentSide_has_external_links hcycle hrefLt hselected).2
  rcases external_cycle_link_five_shape hcycle href hexternal with
    hnext | hselector
  · rcases hnext with ⟨next, hnextMem, hlt, hlinked⟩
    rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
    have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
        vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
    have hnextExternal : CyclePortHasExternalLink vertices next 0 :=
      ⟨incidentVertex ref 5, cycleLinked_symm hnodup hlinked,
        incidentVertex_not_in_later_occurrence hlt (by decide)⟩
    have hnextSelected :=
      cyclePortZeroExternalLink_implies_usesIncidentSide hfull htarget
        (occurrence_lt_of_mem_incidentOccurrences hnextMem) hnextExternal
    obtain ⟨endpoint, hendpointMem, hendpointSelected, hendpointGe,
        selector, hselectorLt, hselectorLinked⟩ :=
      exists_right_selector_endpoint hfull htarget hnextMem hnextSelected
    exact ⟨endpoint, hendpointMem, hendpointSelected,
      Nat.le_trans (Nat.le_of_lt hlt) hendpointGe, selector,
      hselectorLt, hselectorLinked⟩
  · rcases hselector with ⟨selector, hselectorLt, hselectorLinked⟩
    exact ⟨ref, href, hselected, Nat.le_refl _, selector,
      hselectorLt, hselectorLinked⟩
termination_by I.edges.length - ref.occurrence

end CLRS.Chapter34.HamiltonianCycleReduction
