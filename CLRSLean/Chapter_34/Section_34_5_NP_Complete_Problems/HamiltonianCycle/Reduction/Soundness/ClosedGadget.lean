import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.BranchChoices
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CycleBoundary

/-!
# Excluding a closed gadget subcycle

Choosing all four crossing edges would make the twelve vertices of one gadget
a closed cycle.  A Hamiltonian cycle of the nondegenerate reduction also has a
selector vertex, so the general cyclic-boundary theorem rules this pattern out.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def IsOccurrenceWidgetVertex (occurrence vertex : Nat) : Prop :=
  ∃ localVertex, localVertex < widgetVertexCount ∧
    vertex = globalWidgetVertex occurrence localVertex

theorem isOccurrenceWidgetVertex_of_cycleLinked_two
    {vertices : List Nat} {occurrence localVertex first second vertex : Nat}
    (hu : globalWidgetVertex occurrence localVertex ∈ vertices)
    (hfirstLocal : first < widgetVertexCount)
    (hsecondLocal : second < widgetVertexCount)
    (hfirst : CycleLinked vertices (globalWidgetVertex occurrence localVertex)
      (globalWidgetVertex occurrence first))
    (hsecond : CycleLinked vertices (globalWidgetVertex occurrence localVertex)
      (globalWidgetVertex occurrence second))
    (hfirstSecond : first ≠ second)
    (hvertex : CycleLinked vertices (globalWidgetVertex occurrence localVertex)
      vertex) :
    IsOccurrenceWidgetVertex occurrence vertex := by
  have hglobalNe : globalWidgetVertex occurrence first ≠
      globalWidgetVertex occurrence second := by
    simp only [globalWidgetVertex]
    omega
  rcases eq_or_eq_of_cycleLinked_two hu hfirst hsecond hglobalNe hvertex with
    hvertexEq | hvertexEq
  · exact ⟨first, hfirstLocal, hvertexEq⟩
  · exact ⟨second, hsecondLocal, hvertexEq⟩

theorem not_closed_widget_crossing_pattern
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    ¬(CycleLinked vertices (globalWidgetVertex occurrence 2)
          (globalWidgetVertex occurrence 6) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 3)
          (globalWidgetVertex occurrence 11) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 8)
          (globalWidgetVertex occurrence 0) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 9)
          (globalWidgetVertex occurrence 5)) := by
  rintro ⟨h26, h311, h80, h95⟩
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hone := cycleLinked_globalWidgetVertex_one_pair hfull hoccurrence
  have hfour := cycleLinked_globalWidgetVertex_four_pair hfull hoccurrence
  have hseven := cycleLinked_globalWidgetVertex_seven_pair hfull hoccurrence
  have hten := cycleLinked_globalWidgetVertex_ten_pair hfull hoccurrence
  have hmem (localVertex : Nat) (hlocal : localVertex < widgetVertexCount) :
      globalWidgetVertex occurrence localVertex ∈ vertices :=
    globalWidgetVertex_mem_of_representsHamiltonianCycle
      hfull hoccurrence hlocal
  have hinside : ∃ vertex ∈ vertices,
      IsOccurrenceWidgetVertex occurrence vertex := by
    exact ⟨globalWidgetVertex occurrence 0, hmem 0 (by decide),
      0, by decide, rfl⟩
  have hclosed : ∀ u, u ∈ vertices → IsOccurrenceWidgetVertex occurrence u →
      ∀ v, CycleLinked vertices u v →
        IsOccurrenceWidgetVertex occurrence v := by
    rintro _ hu ⟨localVertex, hlocal, rfl⟩ v hlinked
    simp only [widgetVertexCount] at hlocal
    interval_cases localVertex
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hone.1)
        (cycleLinked_symm hnodup h80) (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide) hone.1 hone.2 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hone.2) h26 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hfour.1) h311 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide) hfour.1 hfour.2 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hfour.2)
        (cycleLinked_symm hnodup h95) (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hseven.1)
        (cycleLinked_symm hnodup h26) (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide) hseven.1 hseven.2 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hseven.2) h80 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hten.1) h95 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide) hten.1 hten.2 (by decide) hlinked
    · exact isOccurrenceWidgetVertex_of_cycleLinked_two hu
        (by decide) (by decide)
        (cycleLinked_symm hnodup hten.2)
        (cycleLinked_symm hnodup h311) (by decide) hlinked
  let selector := selectorVertex I.edges.length 0
  have hselectorLt : selector < (clrsHamiltonianInstance I).vertexCount := by
    simp only [selector, selectorVertex, clrsHamiltonianInstance_vertexCount,
      selectorBase]
    omega
  have hselectorMem : selector ∈ vertices :=
    CliqueInstance.mem_of_lt_of_full_cycle_list hnodup hlength hbound
      hselectorLt
  have hselectorOutside : ¬IsOccurrenceWidgetVertex occurrence selector := by
    rintro ⟨localVertex, hlocal, heq⟩
    have hgadget := globalWidgetVertex_lt_selectorBase hoccurrence hlocal
    simp only [selector, selectorVertex] at heq
    omega
  have hall := all_mem_of_cycleLinked_closed hnodup hinside hclosed
  exact hselectorOutside (hall selector hselectorMem)

end CLRS.Chapter34.HamiltonianCycleReduction
