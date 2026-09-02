import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.WidgetCoverage

/-!
# Full vertex coverage of the cover-induced certificate

The certificate builder interleaves selectors with source-vertex paths and
then appends unused selectors.  Here that executable order is permuted into
the canonical order consisting of every gadget vertex followed by every
selector vertex.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem selectedCoverPathFrom_perm_widgets_append_selectors
    (I : CliqueInstance) (cover : Finset Nat) :
    ∀ (selector : Nat) (vertices : List Nat),
      List.Perm (selectedCoverPathFrom I cover selector vertices)
        (vertices.flatMap (selectedSourceVertexPath I cover) ++
          (List.range' selector vertices.length).map
            (selectorVertex I.edges.length)) := by
  intro selector vertices
  induction vertices generalizing selector with
  | nil => simp [selectedCoverPathFrom]
  | cons u vertices ih =>
      have htail := (ih (selector + 1)).append_left
        (selectedSourceVertexPath I cover u)
      have hcons := htail.cons (selectorVertex I.edges.length selector)
      have hmove := (List.perm_middle
        (l₁ := selectedSourceVertexPath I cover u ++
          vertices.flatMap (selectedSourceVertexPath I cover))
        (a := selectorVertex I.edges.length selector)
        (l₂ := (List.range' (selector + 1) vertices.length).map
          (selectorVertex I.edges.length))).symm
      have hcons' : List.Perm
          (selectedCoverPathFrom I cover selector (u :: vertices))
          (selectorVertex I.edges.length selector ::
            ((selectedSourceVertexPath I cover u ++
              vertices.flatMap (selectedSourceVertexPath I cover)) ++
              (List.range' (selector + 1) vertices.length).map
                (selectorVertex I.edges.length))) := by
        simpa [selectedCoverPathFrom, List.range'_succ,
          List.append_assoc] using hcons
      simpa [List.range'_succ, List.append_assoc] using hcons'.trans hmove

theorem selectedCoverPathFrom_active_perm
    (I : CliqueInstance) (cover : Finset Nat) :
    List.Perm
      (selectedCoverPathFrom I cover 0 (activeCoverVertices I cover))
      (selectedCoverWidgetVertices I cover ++
        (List.range (activeCoverVertices I cover).length).map
          (selectorVertex I.edges.length)) := by
  simpa [selectedCoverWidgetVertices_eq_flatMap_active,
    List.range_eq_range'] using
      selectedCoverPathFrom_perm_widgets_append_selectors
        I cover 0 (activeCoverVertices I cover)

theorem usedSelectors_append_unusedSelectorPath
    {I : CliqueInstance} {usedSelectors : Nat}
    (hused : usedSelectors ≤ I.targetSize) :
    (List.range usedSelectors).map (selectorVertex I.edges.length) ++
        unusedSelectorPath I usedSelectors =
      (List.range I.targetSize).map (selectorVertex I.edges.length) := by
  rw [unusedSelectorPath, ← List.map_append, List.range_eq_range',
    List.range_eq_range']
  have happ := @List.range'_append
    (s := 0) (m := usedSelectors) (n := I.targetSize - usedSelectors)
    (step := 1)
  simpa [Nat.add_sub_of_le hused] using congrArg
    (List.map (selectorVertex I.edges.length)) happ

/-- The executable certificate is a permutation of its gadget vertices
followed by every selector. -/
theorem coverHamiltonianCertificate_perm_widget_selector_content
    {I : CliqueInstance} {cover : Finset Nat}
    (hcard : cover.card ≤ I.targetSize) :
    List.Perm (coverHamiltonianCertificate I cover)
      (selectedCoverWidgetVertices I cover ++
        (List.range I.targetSize).map (selectorVertex I.edges.length)) := by
  have hused := activeCoverVertices_length_le_target
    (I := I) (cover := cover) hcard
  have hselected := selectedCoverPathFrom_active_perm I cover
  have happended := hselected.append
    (List.Perm.refl (unusedSelectorPath I (activeCoverVertices I cover).length))
  rw [coverHamiltonianCertificate]
  exact happended.trans (by
    rw [List.append_assoc,
      usedSelectors_append_unusedSelectorPath hused])

theorem map_selectorVertex_range
    (edgeCount selectorCount : Nat) :
    (List.range selectorCount).map (selectorVertex edgeCount) =
      List.range' (selectorBase edgeCount) selectorCount := by
  rw [List.range'_eq_map_range]
  apply List.map_congr_left
  intro selector _
  simp [selectorVertex]

/-- Completeness of the certificate's vertex enumeration: it lists every
target vertex exactly once. -/
theorem coverHamiltonianCertificate_perm_range
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcard : cover.card ≤ I.targetSize)
    (hcover : I.IsVertexCover cover) :
    List.Perm (coverHamiltonianCertificate I cover)
      (List.range (clrsHamiltonianInstance I).vertexCount) := by
  have hcontent := coverHamiltonianCertificate_perm_widget_selector_content
    (I := I) (cover := cover) hcard
  have hwidget := selectedCoverWidgetVertices_perm_range hwellFormed hcover
  have hcanonical := hwidget.append
    (List.Perm.refl
      ((List.range I.targetSize).map (selectorVertex I.edges.length)))
  rw [map_selectorVertex_range] at hcontent hcanonical
  refine hcontent.trans (hcanonical.trans ?_)
  rw [clrsHamiltonianInstance_vertexCount, List.range_eq_range']
  have happ := @List.range'_append
    (s := 0) (m := selectorBase I.edges.length) (n := I.targetSize)
    (step := 1)
  apply List.Perm.of_eq
  simpa [selectorBase, List.range_eq_range'] using happ

theorem coverHamiltonianCertificate_nodup
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcard : cover.card ≤ I.targetSize)
    (hcover : I.IsVertexCover cover) :
    (coverHamiltonianCertificate I cover).Nodup := by
  exact (coverHamiltonianCertificate_perm_range
    hwellFormed hcard hcover).nodup_iff.mpr List.nodup_range

theorem coverHamiltonianCertificate_length
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcard : cover.card ≤ I.targetSize)
    (hcover : I.IsVertexCover cover) :
    (coverHamiltonianCertificate I cover).length =
      (clrsHamiltonianInstance I).vertexCount := by
  simpa using (coverHamiltonianCertificate_perm_range
    hwellFormed hcard hcover).length_eq

theorem coverHamiltonianCertificate_vertex_lt
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcard : cover.card ≤ I.targetSize)
    (hcover : I.IsVertexCover cover) {vertex : Nat}
    (hvertex : vertex ∈ coverHamiltonianCertificate I cover) :
    vertex < (clrsHamiltonianInstance I).vertexCount := by
  have hmem := (coverHamiltonianCertificate_perm_range
    hwellFormed hcard hcover).mem_iff.mp hvertex
  simpa using hmem

end CLRS.Chapter34.HamiltonianCycleReduction
