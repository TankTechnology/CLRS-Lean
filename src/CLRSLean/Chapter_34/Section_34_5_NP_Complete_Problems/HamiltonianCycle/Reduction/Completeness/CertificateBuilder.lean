import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.SelectorLinks
import Mathlib.Data.Finset.Sort

/-!
# Executable Hamiltonian certificate induced by a vertex cover

Isolated vertices in a cover do not own target paths and are removed.  The
remaining vertices are paired with selectors `0,1,...`; unused selectors are
then appended.  This represents the chapter's at-most-`k` cover convention
without arbitrarily padding the source cover.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Cover vertices that own at least one incidence path in the target graph. -/
def activeCoverVertices (I : CliqueInstance) (cover : Finset Nat) : List Nat :=
  (cover.sort (· ≤ ·)).filter fun u => decide (incidentOccurrences I u ≠ [])

/-- Interleave consecutive selector vertices with the source-vertex paths
they select. -/
def selectedCoverPathFrom
    (I : CliqueInstance) (cover : Finset Nat) :
    Nat → List Nat → List Nat
  | _, [] => []
  | selector, u :: vertices =>
      selectorVertex I.edges.length selector ::
        (selectedSourceVertexPath I cover u ++
          selectedCoverPathFrom I cover (selector + 1) vertices)

/-- Selector vertices not used to enter a source-vertex path. -/
def unusedSelectorPath
    (I : CliqueInstance) (usedSelectors : Nat) : List Nat :=
  (List.range' usedSelectors (I.targetSize - usedSelectors)).map
    (selectorVertex I.edges.length)

/-- Ordered Hamiltonian-cycle candidate computed from a typed source cover. -/
def coverHamiltonianCertificate
    (I : CliqueInstance) (cover : Finset Nat) : List Nat :=
  let active := activeCoverVertices I cover
  selectedCoverPathFrom I cover 0 active ++
    unusedSelectorPath I active.length

theorem mem_activeCoverVertices_iff
    {I : CliqueInstance} {cover : Finset Nat} {u : Nat} :
    u ∈ activeCoverVertices I cover ↔
      u ∈ cover ∧ incidentOccurrences I u ≠ [] := by
  simp [activeCoverVertices]

theorem activeCoverVertices_nodup
    (I : CliqueInstance) (cover : Finset Nat) :
    (activeCoverVertices I cover).Nodup := by
  exact (cover.sort_nodup (· ≤ ·)).filter _

theorem activeCoverVertices_length_le_card
    (I : CliqueInstance) (cover : Finset Nat) :
    (activeCoverVertices I cover).length ≤ cover.card := by
  simpa [activeCoverVertices] using
    List.length_filter_le
      (fun u => decide (incidentOccurrences I u ≠ []))
        (cover.sort (· ≤ ·))

theorem activeCoverVertices_length_le_target
    {I : CliqueInstance} {cover : Finset Nat}
    (hcard : cover.card ≤ I.targetSize) :
    (activeCoverVertices I cover).length ≤ I.targetSize :=
  Nat.le_trans (activeCoverVertices_length_le_card I cover) hcard

theorem vertex_lt_of_mem_activeCoverVertices
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover) {u : Nat}
    (hu : u ∈ activeCoverVertices I cover) :
    u < I.vertexCount := by
  exact I.vertex_lt_of_isVertexCover hcover
    (mem_activeCoverVertices_iff.mp hu).1

theorem incidentOccurrences_ne_nil_of_mem_activeCoverVertices
    {I : CliqueInstance} {cover : Finset Nat} {u : Nat}
    (hu : u ∈ activeCoverVertices I cover) :
    incidentOccurrences I u ≠ [] :=
  (mem_activeCoverVertices_iff.mp hu).2

theorem activeCoverVertices_ne_nil_of_edge
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover) (hedges : I.edges ≠ []) :
    activeCoverVertices I cover ≠ [] := by
  obtain ⟨edge, hedge⟩ := List.exists_mem_of_ne_nil I.edges hedges
  rcases I.edge_covered_of_isVertexCover hcover hedge with hleft | hright
  · have hindexed := List.mem_iff_getElem.mp hedge
    rcases hindexed with ⟨i, hi, hedgeEq⟩
    have href : ({ occurrence := i, rightSide := false } : IncidentOccurrence) ∈
        incidentOccurrences I edge.1 := by
      apply leftIncidentOccurrence_mem hi
      simpa [hedgeEq]
    apply List.ne_nil_of_mem
    rw [mem_activeCoverVertices_iff]
    exact ⟨hleft, List.ne_nil_of_mem href⟩
  · have hindexed := List.mem_iff_getElem.mp hedge
    rcases hindexed with ⟨i, hi, hedgeEq⟩
    by_cases hsame : edge.1 = edge.2
    · apply List.ne_nil_of_mem
      rw [mem_activeCoverVertices_iff]
      refine ⟨?_, ?_⟩
      · simpa [hsame] using hright
      · apply List.ne_nil_of_mem
        apply leftIncidentOccurrence_mem hi
        simpa [hedgeEq]
    · have href : ({ occurrence := i, rightSide := true } : IncidentOccurrence) ∈
          incidentOccurrences I edge.2 := by
        apply rightIncidentOccurrence_mem hi
        · simpa [hedgeEq] using hsame
        · simpa [hedgeEq]
      apply List.ne_nil_of_mem
      rw [mem_activeCoverVertices_iff]
      exact ⟨hright, List.ne_nil_of_mem href⟩

theorem selectedCoverPathFrom_head
    (I : CliqueInstance) (cover : Finset Nat)
    (selector u : Nat) (vertices : List Nat) :
    (selectedCoverPathFrom I cover selector (u :: vertices)).head? =
      some (selectorVertex I.edges.length selector) := by
  simp [selectedCoverPathFrom]

theorem unusedSelectorPath_length
    (I : CliqueInstance) (usedSelectors : Nat) :
    (unusedSelectorPath I usedSelectors).length =
      I.targetSize - usedSelectors := by
  simp [unusedSelectorPath]

theorem coverHamiltonianCertificate_selector_count
    (I : CliqueInstance) (cover : Finset Nat) :
    (activeCoverVertices I cover).length +
        (unusedSelectorPath I (activeCoverVertices I cover).length).length =
      max (activeCoverVertices I cover).length I.targetSize := by
  simp [unusedSelectorPath]
  omega

end CLRS.Chapter34.HamiltonianCycleReduction
