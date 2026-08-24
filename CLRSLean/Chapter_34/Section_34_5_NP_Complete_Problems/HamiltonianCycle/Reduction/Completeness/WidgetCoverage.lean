import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.IncidenceCoverage

/-!
# Global gadget-vertex coverage

This file lifts the incidence reindexing theorem to the actual globally
numbered target vertices.  A typed source cover contributes exactly the twelve
vertices of every edge gadget, and contributes each of them exactly once.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Gadget vertices in certificate order, with selectors omitted. -/
def selectedCoverWidgetVertices
    (I : CliqueInstance) (cover : Finset Nat) : List Nat :=
  (selectedCoverOccurrences I cover).flatMap
    (selectedGlobalWidgetPath I cover)

/-- The globally numbered local-coverage block of one edge occurrence. -/
def occurrenceWidgetVertices
    (I : CliqueInstance) (cover : Finset Nat) (occurrence : Nat) : List Nat :=
  (selectedOccurrenceVertices I cover occurrence).map
    (globalWidgetVertex occurrence)

/-- All gadget vertices, grouped in source-edge occurrence order. -/
def coveredWidgetVertices
    (I : CliqueInstance) (cover : Finset Nat) : List Nat :=
  (List.range I.edges.length).flatMap
    (occurrenceWidgetVertices I cover)

theorem selectedCoverWidgetVertices_eq_flatMap_active
    (I : CliqueInstance) (cover : Finset Nat) :
    selectedCoverWidgetVertices I cover =
      (activeCoverVertices I cover).flatMap
        (selectedSourceVertexPath I cover) := by
  rw [selectedCoverWidgetVertices, selectedCoverOccurrences,
    List.flatMap_assoc]
  rfl

theorem flatMap_coveredOccurrenceRefs_selectedGlobalWidgetPath
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (coveredOccurrenceRefs I cover occurrence).flatMap
        (selectedGlobalWidgetPath I cover) =
      occurrenceWidgetVertices I cover occurrence := by
  by_cases hleft : I.edges[occurrence].1 ∈ cover <;>
    by_cases hright : I.edges[occurrence].2 ∈ cover <;>
      simp [coveredOccurrenceRefs, occurrenceWidgetVertices,
        selectedOccurrenceVertices, selectedGlobalWidgetPath, mapWidgetPath,
        sourceEdgeForOccurrence, List.getElem?_eq_getElem hoccurrence,
        leftOccurrence, rightOccurrence, hleft, hright]

theorem flatMap_coveredOccurrences_selectedGlobalWidgetPath
    (I : CliqueInstance) (cover : Finset Nat) :
    (coveredOccurrences I cover).flatMap
        (selectedGlobalWidgetPath I cover) =
      coveredWidgetVertices I cover := by
  rw [coveredOccurrences, List.flatMap_assoc]
  unfold coveredWidgetVertices
  apply List.flatMap_congr
  intro occurrence hoccurrence
  apply flatMap_coveredOccurrenceRefs_selectedGlobalWidgetPath
  simpa using hoccurrence

/-- Incidence reindexing remains a permutation after expanding each incidence
to its chosen gadget traversal. -/
theorem selectedCoverWidgetVertices_perm_coveredWidgetVertices
    {I : CliqueInstance} {cover : Finset Nat} (hwellFormed : I.WellFormed) :
    List.Perm (selectedCoverWidgetVertices I cover)
      (coveredWidgetVertices I cover) := by
  have hperm := (selectedCoverOccurrences_perm_coveredOccurrences
    (I := I) (cover := cover) hwellFormed).flatMap
      (f := selectedGlobalWidgetPath I cover)
      (g := selectedGlobalWidgetPath I cover)
      (fun ref _ => List.Perm.refl _)
  rw [flatMap_coveredOccurrences_selectedGlobalWidgetPath] at hperm
  exact hperm

theorem occurrenceWidgetVertices_nodup
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    (occurrenceWidgetVertices I cover occurrence).Nodup := by
  unfold occurrenceWidgetVertices
  apply (selectedOccurrenceVertices_nodup hoccurrence hcovered).map
  intro first second heq
  simp only [globalWidgetVertex] at heq
  omega

/-- One covered gadget block is a permutation of its twelve consecutive global
vertex numbers. -/
theorem occurrenceWidgetVertices_perm_range'
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    List.Perm (occurrenceWidgetVertices I cover occurrence)
      (List.range' (widgetVertexCount * occurrence) widgetVertexCount) := by
  apply (List.perm_ext_iff_of_nodup
    (occurrenceWidgetVertices_nodup hoccurrence hcovered)
    (List.nodup_range' 1 (by omega))).2
  intro vertex
  simp only [occurrenceWidgetVertices, List.mem_map, List.mem_range']
  constructor
  · rintro ⟨localVertex, hlocal, rfl⟩
    have hbound := (mem_selectedOccurrenceVertices_iff
      hoccurrence hcovered).mp hlocal
    exact ⟨localVertex, hbound, by simp [globalWidgetVertex]⟩
  · rintro ⟨localVertex, hbound, rfl⟩
    refine ⟨localVertex,
      (mem_selectedOccurrenceVertices_iff hoccurrence hcovered).2 hbound, ?_⟩
    simp [globalWidgetVertex]

/-- Concatenating consecutive twelve-vertex blocks gives the initial global
gadget range. -/
theorem flatMap_widgetRanges_eq_range (edgeCount : Nat) :
    (List.range edgeCount).flatMap
        (fun occurrence =>
          List.range' (widgetVertexCount * occurrence) widgetVertexCount) =
      List.range (selectorBase edgeCount) := by
  induction edgeCount with
  | zero => simp [selectorBase]
  | succ edgeCount ih =>
      rw [List.range_succ, List.flatMap_append, ih]
      simp only [List.flatMap_singleton, List.range_eq_range']
      change List.range' 0 (12 * edgeCount) ++
          List.range' (12 * edgeCount) 12 =
        List.range' 0 (12 * (edgeCount + 1))
      calc
        _ = List.range' 0 (12 * edgeCount + 12) := by
          simpa using (@List.range'_append
            (s := 0) (m := 12 * edgeCount) (n := 12) (step := 1))
        _ = _ := by congr 2 <;> omega

theorem coveredWidgetVertices_perm_range
    {I : CliqueInstance} {cover : Finset Nat}
    (hcover : I.IsVertexCover cover) :
    List.Perm (coveredWidgetVertices I cover)
      (List.range (selectorBase I.edges.length)) := by
  have hblocks : List.Perm (coveredWidgetVertices I cover)
      ((List.range I.edges.length).flatMap fun occurrence =>
        List.range' (widgetVertexCount * occurrence) widgetVertexCount) := by
    unfold coveredWidgetVertices
    apply (List.Perm.refl (List.range I.edges.length)).flatMap
    intro occurrence hoccurrence
    have hoccurrence' : occurrence < I.edges.length := by
      simpa using hoccurrence
    apply occurrenceWidgetVertices_perm_range' hoccurrence'
    exact I.edge_covered_of_isVertexCover hcover
      (List.getElem_mem hoccurrence')
  rw [flatMap_widgetRanges_eq_range] at hblocks
  exact hblocks

/-- The gadget-only projection of the certificate contains precisely every
global gadget vertex once. -/
theorem selectedCoverWidgetVertices_perm_range
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcover : I.IsVertexCover cover) :
    List.Perm (selectedCoverWidgetVertices I cover)
      (List.range (selectorBase I.edges.length)) := by
  exact (selectedCoverWidgetVertices_perm_coveredWidgetVertices hwellFormed).trans
    (coveredWidgetVertices_perm_range hcover)

theorem selectedCoverWidgetVertices_nodup
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcover : I.IsVertexCover cover) :
    (selectedCoverWidgetVertices I cover).Nodup := by
  exact (selectedCoverWidgetVertices_perm_range hwellFormed hcover).nodup_iff.mpr
    List.nodup_range

theorem selectedCoverWidgetVertices_length
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcover : I.IsVertexCover cover) :
    (selectedCoverWidgetVertices I cover).length = selectorBase I.edges.length := by
  simpa using (selectedCoverWidgetVertices_perm_range
    hwellFormed hcover).length_eq

theorem mem_selectedCoverWidgetVertices_iff
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcover : I.IsVertexCover cover)
    {vertex : Nat} :
    vertex ∈ selectedCoverWidgetVertices I cover ↔
      vertex < selectorBase I.edges.length := by
  exact (selectedCoverWidgetVertices_perm_range hwellFormed hcover).mem_iff.trans
    List.mem_range

end CLRS.Chapter34.HamiltonianCycleReduction
