import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CycleEdges

/-!
# Forced choices at the four branching vertices

The degree-two core fixes one cycle edge incident to each branching vertex.
Its remaining cycle edge must therefore choose one of the two remaining
local gadget neighbors.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem cycleLinked_globalWidgetVertex_one_pair
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 1)
        (globalWidgetVertex occurrence 0) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 1)
        (globalWidgetVertex occurrence 2) := by
  let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hcycle hoccurrence (show 1 < widgetVertexCount by decide)
  exact cycleLinked_pair_of_neighbors hmem
    (cycle_neighbors_globalWidgetVertex_one hcycle hoccurrence)

theorem cycleLinked_globalWidgetVertex_four_pair
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 4)
        (globalWidgetVertex occurrence 3) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 4)
        (globalWidgetVertex occurrence 5) := by
  let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hcycle hoccurrence (show 4 < widgetVertexCount by decide)
  exact cycleLinked_pair_of_neighbors hmem
    (cycle_neighbors_globalWidgetVertex_four hcycle hoccurrence)

theorem cycleLinked_globalWidgetVertex_seven_pair
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 7)
        (globalWidgetVertex occurrence 6) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 7)
        (globalWidgetVertex occurrence 8) := by
  let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hcycle hoccurrence (show 7 < widgetVertexCount by decide)
  exact cycleLinked_pair_of_neighbors hmem
    (cycle_neighbors_globalWidgetVertex_seven hcycle hoccurrence)

theorem cycleLinked_globalWidgetVertex_ten_pair
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 10)
        (globalWidgetVertex occurrence 9) ∧
      CycleLinked vertices (globalWidgetVertex occurrence 10)
        (globalWidgetVertex occurrence 11) := by
  let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hcycle hoccurrence (show 10 < widgetVertexCount by decide)
  exact cycleLinked_pair_of_neighbors hmem
    (cycle_neighbors_globalWidgetVertex_ten hcycle hoccurrence)

theorem cycleLinked_globalWidgetVertex_two_choice
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 2)
        (globalWidgetVertex occurrence 3) ∨
      CycleLinked vertices (globalWidgetVertex occurrence 2)
        (globalWidgetVertex occurrence 6) := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 2 < widgetVertexCount by decide)
  apply cycleLinked_other_of_adj_iff_three hnodup
    (by simpa [hlength] using hthree) hcycleAdjacent hmem
    (fun vertex => adj_globalWidgetVertex_two_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)
  exact cycleLinked_symm hnodup
    (cycleLinked_globalWidgetVertex_one_pair hfull hoccurrence).2

theorem cycleLinked_globalWidgetVertex_three_choice
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 3)
        (globalWidgetVertex occurrence 2) ∨
      CycleLinked vertices (globalWidgetVertex occurrence 3)
        (globalWidgetVertex occurrence 11) := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 3 < widgetVertexCount by decide)
  apply cycleLinked_other_of_adj_iff_three hnodup
    (by simpa [hlength] using hthree) hcycleAdjacent hmem
    (fun vertex => by
      rw [adj_globalWidgetVertex_three_iff
        (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence]
      aesop)
  exact cycleLinked_symm hnodup
    (cycleLinked_globalWidgetVertex_four_pair hfull hoccurrence).1

theorem cycleLinked_globalWidgetVertex_eight_choice
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 8)
        (globalWidgetVertex occurrence 9) ∨
      CycleLinked vertices (globalWidgetVertex occurrence 8)
        (globalWidgetVertex occurrence 0) := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 8 < widgetVertexCount by decide)
  apply cycleLinked_other_of_adj_iff_three hnodup
    (by simpa [hlength] using hthree) hcycleAdjacent hmem
    (fun vertex => adj_globalWidgetVertex_eight_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)
  exact cycleLinked_symm hnodup
    (cycleLinked_globalWidgetVertex_seven_pair hfull hoccurrence).2

theorem cycleLinked_globalWidgetVertex_nine_choice
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    CycleLinked vertices (globalWidgetVertex occurrence 9)
        (globalWidgetVertex occurrence 8) ∨
      CycleLinked vertices (globalWidgetVertex occurrence 9)
        (globalWidgetVertex occurrence 5) := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hfull : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices := ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  have hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
    hfull hoccurrence (show 9 < widgetVertexCount by decide)
  apply cycleLinked_other_of_adj_iff_three hnodup
    (by simpa [hlength] using hthree) hcycleAdjacent hmem
    (fun vertex => by
      rw [adj_globalWidgetVertex_nine_iff
        (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence]
      aesop)
  exact cycleLinked_symm hnodup
    (cycleLinked_globalWidgetVertex_ten_pair hfull hoccurrence).1

end CLRS.Chapter34.HamiltonianCycleReduction
