import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.CoreNeighbors

/-!
# Forced cyclic neighbors at gadget-core vertices

Every gadget vertex occurs in a Hamiltonian certificate.  Combining this full
coverage with the exact degree-two neighborhood interface fixes the cyclic
predecessor and successor of each core vertex, up to orientation.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem globalWidgetVertex_mem_of_representsHamiltonianCycle
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hlocalVertex : localVertex < widgetVertexCount) :
    globalWidgetVertex occurrence localVertex ∈ vertices := by
  rcases hcycle with ⟨_, hnodup, hlength, hbound, _⟩
  apply CliqueInstance.mem_of_lt_of_full_cycle_list hnodup hlength hbound
  have hgadget := globalWidgetVertex_lt_selectorBase
    hoccurrence hlocalVertex
  rw [clrsHamiltonianInstance_vertexCount]
  simp only [selectorBase] at hgadget
  omega

theorem cycle_neighbors_globalWidgetVertex_of_adj_iff_pair
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence localVertex left right : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hlocalVertex : localVertex < widgetVertexCount)
    (hadj : ∀ vertex,
      (clrsHamiltonianInstance I).Adj
          (globalWidgetVertex occurrence localVertex) vertex ↔
        vertex = globalWidgetVertex occurrence left ∨
        vertex = globalWidgetVertex occurrence right) :
    (vertices.next (globalWidgetVertex occurrence localVertex)
          (globalWidgetVertex_mem_of_representsHamiltonianCycle
            hcycle hoccurrence hlocalVertex) =
        globalWidgetVertex occurrence left ∧
      vertices.prev (globalWidgetVertex occurrence localVertex)
          (globalWidgetVertex_mem_of_representsHamiltonianCycle
            hcycle hoccurrence hlocalVertex) =
        globalWidgetVertex occurrence right) ∨
    (vertices.next (globalWidgetVertex occurrence localVertex)
          (globalWidgetVertex_mem_of_representsHamiltonianCycle
            hcycle hoccurrence hlocalVertex) =
        globalWidgetVertex occurrence right ∧
      vertices.prev (globalWidgetVertex occurrence localVertex)
          (globalWidgetVertex_mem_of_representsHamiltonianCycle
            hcycle hoccurrence hlocalVertex) =
        globalWidgetVertex occurrence left) := by
  rcases hcycle with ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
  exact CliqueInstance.cycle_neighbors_of_adj_iff_pair
    (I := clrsHamiltonianInstance I)
    (v := globalWidgetVertex occurrence localVertex)
    (left := globalWidgetVertex occurrence left)
    (right := globalWidgetVertex occurrence right)
    hnodup
    (by simpa [hlength] using hthree)
    hcycleAdjacent
    (globalWidgetVertex_mem_of_representsHamiltonianCycle
      ⟨hthree, hnodup, hlength, hbound, hcycleAdjacent⟩
      hoccurrence hlocalVertex)
    hadj

theorem cycle_neighbors_globalWidgetVertex_one
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
      hcycle hoccurrence (show 1 < widgetVertexCount by decide)
    (vertices.next (globalWidgetVertex occurrence 1) hmem =
        globalWidgetVertex occurrence 0 ∧
      vertices.prev (globalWidgetVertex occurrence 1) hmem =
        globalWidgetVertex occurrence 2) ∨
    (vertices.next (globalWidgetVertex occurrence 1) hmem =
        globalWidgetVertex occurrence 2 ∧
      vertices.prev (globalWidgetVertex occurrence 1) hmem =
        globalWidgetVertex occurrence 0) := by
  exact cycle_neighbors_globalWidgetVertex_of_adj_iff_pair
    hcycle hoccurrence (by decide)
    (fun vertex => adj_globalWidgetVertex_one_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)

theorem cycle_neighbors_globalWidgetVertex_four
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
      hcycle hoccurrence (show 4 < widgetVertexCount by decide)
    (vertices.next (globalWidgetVertex occurrence 4) hmem =
        globalWidgetVertex occurrence 3 ∧
      vertices.prev (globalWidgetVertex occurrence 4) hmem =
        globalWidgetVertex occurrence 5) ∨
    (vertices.next (globalWidgetVertex occurrence 4) hmem =
        globalWidgetVertex occurrence 5 ∧
      vertices.prev (globalWidgetVertex occurrence 4) hmem =
        globalWidgetVertex occurrence 3) := by
  exact cycle_neighbors_globalWidgetVertex_of_adj_iff_pair
    hcycle hoccurrence (by decide)
    (fun vertex => adj_globalWidgetVertex_four_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)

theorem cycle_neighbors_globalWidgetVertex_seven
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
      hcycle hoccurrence (show 7 < widgetVertexCount by decide)
    (vertices.next (globalWidgetVertex occurrence 7) hmem =
        globalWidgetVertex occurrence 6 ∧
      vertices.prev (globalWidgetVertex occurrence 7) hmem =
        globalWidgetVertex occurrence 8) ∨
    (vertices.next (globalWidgetVertex occurrence 7) hmem =
        globalWidgetVertex occurrence 8 ∧
      vertices.prev (globalWidgetVertex occurrence 7) hmem =
        globalWidgetVertex occurrence 6) := by
  exact cycle_neighbors_globalWidgetVertex_of_adj_iff_pair
    hcycle hoccurrence (by decide)
    (fun vertex => adj_globalWidgetVertex_seven_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)

theorem cycle_neighbors_globalWidgetVertex_ten
    {I : CliqueInstance} {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    {occurrence : Nat} (hoccurrence : occurrence < I.edges.length) :
    let hmem := globalWidgetVertex_mem_of_representsHamiltonianCycle
      hcycle hoccurrence (show 10 < widgetVertexCount by decide)
    (vertices.next (globalWidgetVertex occurrence 10) hmem =
        globalWidgetVertex occurrence 9 ∧
      vertices.prev (globalWidgetVertex occurrence 10) hmem =
        globalWidgetVertex occurrence 11) ∨
    (vertices.next (globalWidgetVertex occurrence 10) hmem =
        globalWidgetVertex occurrence 11 ∧
      vertices.prev (globalWidgetVertex occurrence 10) hmem =
        globalWidgetVertex occurrence 9) := by
  exact cycle_neighbors_globalWidgetVertex_of_adj_iff_pair
    hcycle hoccurrence (by decide)
    (fun vertex => adj_globalWidgetVertex_ten_iff
      (I := I) (occurrence := occurrence) (vertex := vertex) hoccurrence)

end CLRS.Chapter34.HamiltonianCycleReduction
