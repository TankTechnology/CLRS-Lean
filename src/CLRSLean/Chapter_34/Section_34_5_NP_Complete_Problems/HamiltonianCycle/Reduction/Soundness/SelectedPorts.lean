import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.SourceCover
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.SameGadgetNeighbors

/-!
# External links at selected gadget ports

When a Hamiltonian cycle uses one side of an edge gadget, both endpoint ports
of that side spend exactly one cycle edge inside the gadget.  Their other
cycle edges must leave the occurrence block.  This is the local interface
needed to propagate selection along source-vertex incidence chains.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def CyclePortHasExternalLink
    (vertices : List Nat) (ref : IncidentOccurrence) (position : Nat) : Prop :=
  ∃ vertex,
    CycleLinked vertices (incidentVertex ref position) vertex ∧
      ¬IsOccurrenceWidgetVertex ref.occurrence vertex

theorem exists_external_cycle_neighbor_of_port
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence port fixed crossing : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hport : port < widgetVertexCount)
    (hfixed : CycleLinked vertices
      (globalWidgetVertex occurrence port)
      (globalWidgetVertex occurrence fixed))
    (hnotCrossing : ¬CycleLinked vertices
      (globalWidgetVertex occurrence port)
      (globalWidgetVertex occurrence crossing))
    (hadj : ∀ localNeighbor,
      widgetInstance.Adj port localNeighbor ↔
        localNeighbor = fixed ∨ localNeighbor = crossing) :
    ∃ vertex,
      CycleLinked vertices (globalWidgetVertex occurrence port) vertex ∧
        ¬IsOccurrenceWidgetVertex occurrence vertex := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence hport
  obtain ⟨vertex, hlinked, hne⟩ := exists_cycleLinked_ne_of_cycleLinked
    hnodup (by simpa [hlength] using hthree) hmem hfixed
  refine ⟨vertex, hlinked, ?_⟩
  rintro ⟨localNeighbor, hlocal, rfl⟩
  have hlocalAdj : widgetInstance.Adj port localNeighbor :=
    (adj_same_globalWidgetOccurrence_iff hoccurrence hport hlocal).mp
      (adj_of_cycleLinked hnodup hcycleAdjacent hlinked)
  rcases (hadj localNeighbor).mp hlocalAdj with rfl | rfl
  · exact hne rfl
  · exact hnotCrossing hlinked

theorem widgetInstance_adj_zero_iff (localNeighbor : Nat) :
    widgetInstance.Adj 0 localNeighbor ↔
      localNeighbor = 1 ∨ localNeighbor = 8 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  omega

theorem widgetInstance_adj_five_iff (localNeighbor : Nat) :
    widgetInstance.Adj 5 localNeighbor ↔
      localNeighbor = 4 ∨ localNeighbor = 9 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_six_iff (localNeighbor : Nat) :
    widgetInstance.Adj 6 localNeighbor ↔
      localNeighbor = 7 ∨ localNeighbor = 2 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_eleven_iff (localNeighbor : Nat) :
    widgetInstance.Adj 11 localNeighbor ↔
      localNeighbor = 10 ∨ localNeighbor = 3 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  omega

theorem cyclePortHasExternalLink_left
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length)
    (h89 : CycleLinked vertices (globalWidgetVertex occurrence 8)
      (globalWidgetVertex occurrence 9)) :
    CyclePortHasExternalLink vertices
        { occurrence := occurrence, rightSide := false } 0 ∧
      CyclePortHasExternalLink vertices
        { occurrence := occurrence, rightSide := false } 5 := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hone := cycleLinked_globalWidgetVertex_one_pair hfull hoccurrence
  have hfour := cycleLinked_globalWidgetVertex_four_pair hfull hoccurrence
  have hseven := cycleLinked_globalWidgetVertex_seven_pair hfull hoccurrence
  have hten := cycleLinked_globalWidgetVertex_ten_pair hfull hoccurrence
  have hmem8 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 8 < widgetVertexCount by decide)
  have hmem9 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 9 < widgetVertexCount by decide)
  have hnot80 : ¬CycleLinked vertices (globalWidgetVertex occurrence 8)
      (globalWidgetVertex occurrence 0) :=
    not_cycleLinked_of_two hmem8
      (cycleLinked_symm hnodup hseven.2) h89
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
  have hnot59 : ¬CycleLinked vertices (globalWidgetVertex occurrence 5)
      (globalWidgetVertex occurrence 9) := by
    intro h59
    exact not_cycleLinked_of_two hmem9
      (cycleLinked_symm hnodup h89)
      (cycleLinked_symm hnodup hten.1)
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (cycleLinked_symm hnodup h59)
  constructor
  · simpa [CyclePortHasExternalLink, incidentVertex, widgetVertex] using
      (exists_external_cycle_neighbor_of_port hfull hoccurrence
        (show 0 < widgetVertexCount by decide)
        (cycleLinked_symm hnodup hone.1)
        (fun h08 => hnot80 (cycleLinked_symm hnodup h08))
        widgetInstance_adj_zero_iff)
  · simpa [CyclePortHasExternalLink, incidentVertex, widgetVertex] using
      (exists_external_cycle_neighbor_of_port hfull hoccurrence
        (show 5 < widgetVertexCount by decide)
        (cycleLinked_symm hnodup hfour.2) hnot59
        widgetInstance_adj_five_iff)

theorem cyclePortHasExternalLink_right
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length)
    (h23 : CycleLinked vertices (globalWidgetVertex occurrence 2)
      (globalWidgetVertex occurrence 3)) :
    CyclePortHasExternalLink vertices
        { occurrence := occurrence, rightSide := true } 0 ∧
      CyclePortHasExternalLink vertices
        { occurrence := occurrence, rightSide := true } 5 := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hone := cycleLinked_globalWidgetVertex_one_pair hfull hoccurrence
  have hfour := cycleLinked_globalWidgetVertex_four_pair hfull hoccurrence
  have hseven := cycleLinked_globalWidgetVertex_seven_pair hfull hoccurrence
  have hten := cycleLinked_globalWidgetVertex_ten_pair hfull hoccurrence
  have hmem2 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 2 < widgetVertexCount by decide)
  have hmem3 := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 3 < widgetVertexCount by decide)
  have hnot62 : ¬CycleLinked vertices (globalWidgetVertex occurrence 6)
      (globalWidgetVertex occurrence 2) := by
    intro h62
    exact not_cycleLinked_of_two hmem2
      (cycleLinked_symm hnodup hone.2) h23
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (cycleLinked_symm hnodup h62)
  have hnot113 : ¬CycleLinked vertices (globalWidgetVertex occurrence 11)
      (globalWidgetVertex occurrence 3) := by
    intro h113
    exact not_cycleLinked_of_two hmem3
      (cycleLinked_symm hnodup h23)
      (cycleLinked_symm hnodup hfour.1)
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (by simp [globalWidgetVertex])
      (cycleLinked_symm hnodup h113)
  constructor
  · simpa [CyclePortHasExternalLink, incidentVertex, widgetVertex] using
      (exists_external_cycle_neighbor_of_port hfull hoccurrence
        (show 6 < widgetVertexCount by decide)
        (cycleLinked_symm hnodup hseven.1) hnot62
        widgetInstance_adj_six_iff)
  · simpa [CyclePortHasExternalLink, incidentVertex, widgetVertex] using
      (exists_external_cycle_neighbor_of_port hfull hoccurrence
        (show 11 < widgetVertexCount by decide)
        (cycleLinked_symm hnodup hten.2) hnot113
        widgetInstance_adj_eleven_iff)

theorem cycleUsesIncidentSide_has_external_links
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {ref : IncidentOccurrence} (href : ref.occurrence < I.edges.length)
    (hselected : CycleUsesIncidentSide vertices ref) :
    CyclePortHasExternalLink vertices ref 0 ∧
      CyclePortHasExternalLink vertices ref 5 := by
  cases ref with
  | mk occurrence rightSide =>
      cases rightSide with
      | false =>
          simp only [CycleUsesIncidentSide, Bool.false_eq_true, ↓reduceIte]
            at hselected
          rcases hselected with hsplit | hleftFull
          · exact cyclePortHasExternalLink_left hcycle href hsplit.2
          · exact cyclePortHasExternalLink_left hcycle href hleftFull.2.2
      | true =>
          simp only [CycleUsesIncidentSide, ↓reduceIte] at hselected
          rcases hselected with hsplit | hrightFull
          · exact cyclePortHasExternalLink_right hcycle href hsplit.1
          · exact cyclePortHasExternalLink_right hcycle href hrightFull.1

theorem cyclePortFiveExternalLink_implies_usesIncidentSide
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {ref : IncidentOccurrence} (href : ref.occurrence < I.edges.length)
    (hexternal : CyclePortHasExternalLink vertices ref 5) :
    CycleUsesIncidentSide vertices ref := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  rcases hexternal with ⟨vertex, hlinked, houtside⟩
  cases ref with
  | mk occurrence rightSide =>
      rcases cycle_uses_allowed_widget_traversal hfull htarget href with
        hsplit | hleftFull | hrightFull
      · cases rightSide <;> simp [CycleUsesIncidentSide, hsplit]
      · cases rightSide with
        | false => simp [CycleUsesIncidentSide, hleftFull]
        | true =>
            have hten := cycleLinked_globalWidgetVertex_ten_pair hfull href
            have hmem11 := globalWidgetVertex_mem_of_representsHamiltonianCycle
              hfull href (show 11 < widgetVertexCount by decide)
            have hlinked' : CycleLinked vertices
                (globalWidgetVertex occurrence 11) vertex := by
              simpa [incidentVertex, widgetVertex] using hlinked
            have hinside := eq_or_eq_of_cycleLinked_two hmem11
              (cycleLinked_symm hnodup hten.2)
              (cycleLinked_symm hnodup hleftFull.2.1)
              (by simp [globalWidgetVertex]) hlinked'
            apply (houtside ?_).elim
            rcases hinside with rfl | rfl
            · exact ⟨10, by decide, rfl⟩
            · exact ⟨3, by decide, rfl⟩
      · cases rightSide with
        | true => simp [CycleUsesIncidentSide, hrightFull]
        | false =>
            have hfour := cycleLinked_globalWidgetVertex_four_pair hfull href
            have hmem5 := globalWidgetVertex_mem_of_representsHamiltonianCycle
              hfull href (show 5 < widgetVertexCount by decide)
            have hlinked' : CycleLinked vertices
                (globalWidgetVertex occurrence 5) vertex := by
              simpa [incidentVertex, widgetVertex] using hlinked
            have hinside := eq_or_eq_of_cycleLinked_two hmem5
              (cycleLinked_symm hnodup hfour.2)
              (cycleLinked_symm hnodup hrightFull.2.2)
              (by simp [globalWidgetVertex]) hlinked'
            apply (houtside ?_).elim
            rcases hinside with rfl | rfl
            · exact ⟨4, by decide, rfl⟩
            · exact ⟨9, by decide, rfl⟩

theorem cyclePortZeroExternalLink_implies_usesIncidentSide
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {ref : IncidentOccurrence} (href : ref.occurrence < I.edges.length)
    (hexternal : CyclePortHasExternalLink vertices ref 0) :
    CycleUsesIncidentSide vertices ref := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  rcases hexternal with ⟨vertex, hlinked, houtside⟩
  cases ref with
  | mk occurrence rightSide =>
      rcases cycle_uses_allowed_widget_traversal hfull htarget href with
        hsplit | hleftFull | hrightFull
      · cases rightSide <;> simp [CycleUsesIncidentSide, hsplit]
      · cases rightSide with
        | false => simp [CycleUsesIncidentSide, hleftFull]
        | true =>
            have hseven := cycleLinked_globalWidgetVertex_seven_pair hfull href
            have hmem6 := globalWidgetVertex_mem_of_representsHamiltonianCycle
              hfull href (show 6 < widgetVertexCount by decide)
            have hlinked' : CycleLinked vertices
                (globalWidgetVertex occurrence 6) vertex := by
              simpa [incidentVertex, widgetVertex] using hlinked
            have hinside := eq_or_eq_of_cycleLinked_two hmem6
              (cycleLinked_symm hnodup hseven.1)
              (cycleLinked_symm hnodup hleftFull.1)
              (by simp [globalWidgetVertex]) hlinked'
            apply (houtside ?_).elim
            rcases hinside with rfl | rfl
            · exact ⟨7, by decide, rfl⟩
            · exact ⟨2, by decide, rfl⟩
      · cases rightSide with
        | true => simp [CycleUsesIncidentSide, hrightFull]
        | false =>
            have hone := cycleLinked_globalWidgetVertex_one_pair hfull href
            have hmem0 := globalWidgetVertex_mem_of_representsHamiltonianCycle
              hfull href (show 0 < widgetVertexCount by decide)
            have hlinked' : CycleLinked vertices
                (globalWidgetVertex occurrence 0) vertex := by
              simpa [incidentVertex, widgetVertex] using hlinked
            have hinside := eq_or_eq_of_cycleLinked_two hmem0
              (cycleLinked_symm hnodup hone.1)
              (cycleLinked_symm hnodup hrightFull.2.1)
              (by simp [globalWidgetVertex]) hlinked'
            apply (houtside ?_).elim
            rcases hinside with rfl | rfl
            · exact ⟨1, by decide, rfl⟩
            · exact ⟨8, by decide, rfl⟩

end CLRS.Chapter34.HamiltonianCycleReduction
