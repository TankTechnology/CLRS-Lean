import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.CertificateAdjacency

/-!
# Exact local coverage supplied by a source cover

For one source-edge occurrence, the selected endpoint paths have exactly one
of the three CLRS shapes: a full traversal entered from the left, a full
traversal entered from the right, or the two disjoint six-vertex side paths.
All three shapes enumerate the twelve local gadget vertices exactly once.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Left-side incidence reference for a source-edge occurrence. -/
def leftOccurrence (occurrence : Nat) : IncidentOccurrence :=
  { occurrence := occurrence, rightSide := false }

/-- Right-side incidence reference for a source-edge occurrence. -/
def rightOccurrence (occurrence : Nat) : IncidentOccurrence :=
  { occurrence := occurrence, rightSide := true }

/-- Local gadget vertices contributed by the selected endpoints of one source
edge occurrence. -/
def selectedOccurrenceVertices
    (I : CliqueInstance) (cover : Finset Nat) (occurrence : Nat) : List Nat :=
  let edge := sourceEdgeForOccurrence I (leftOccurrence occurrence)
  (if edge.1 ∈ cover then
      selectedWidgetPath I cover (leftOccurrence occurrence)
    else []) ++
  (if edge.2 ∈ cover then
      selectedWidgetPath I cover (rightOccurrence occurrence)
    else [])

theorem sourceEdgeForOccurrence_leftOccurrence
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    sourceEdgeForOccurrence I (leftOccurrence occurrence) =
      I.edges[occurrence] := by
  exact sourceEdgeForOccurrence_eq_getElem hoccurrence

theorem sourceEdgeForOccurrence_rightOccurrence
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    sourceEdgeForOccurrence I (rightOccurrence occurrence) =
      I.edges[occurrence] := by
  exact sourceEdgeForOccurrence_eq_getElem hoccurrence

theorem otherEndpoint_leftOccurrence
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    otherEndpoint I (leftOccurrence occurrence) = I.edges[occurrence].2 := by
  change (sourceEdgeForOccurrence I (leftOccurrence occurrence)).2 = _
  rw [sourceEdgeForOccurrence_leftOccurrence hoccurrence]

theorem otherEndpoint_rightOccurrence
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    otherEndpoint I (rightOccurrence occurrence) = I.edges[occurrence].1 := by
  change (sourceEdgeForOccurrence I (rightOccurrence occurrence)).1 = _
  rw [sourceEdgeForOccurrence_rightOccurrence hoccurrence]

theorem selectedWidgetPath_leftOccurrence
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    selectedWidgetPath I cover (leftOccurrence occurrence) =
      if I.edges[occurrence].2 ∈ cover then widgetLeftPath
      else widgetLeftFullPath := by
  change (if otherEndpoint I (leftOccurrence occurrence) ∈ cover then
      widgetLeftPath else widgetLeftFullPath) = _
  rw [otherEndpoint_leftOccurrence hoccurrence]

theorem selectedWidgetPath_rightOccurrence
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    selectedWidgetPath I cover (rightOccurrence occurrence) =
      if I.edges[occurrence].1 ∈ cover then widgetRightPath
      else widgetRightFullPath := by
  change (if otherEndpoint I (rightOccurrence occurrence) ∈ cover then
      widgetRightPath else widgetRightFullPath) = _
  rw [otherEndpoint_rightOccurrence hoccurrence]

theorem selectedOccurrenceVertices_shape
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    selectedOccurrenceVertices I cover occurrence = widgetLeftFullPath ∨
      selectedOccurrenceVertices I cover occurrence = widgetRightFullPath ∨
      selectedOccurrenceVertices I cover occurrence =
        widgetLeftPath ++ widgetRightPath := by
  by_cases hleft : I.edges[occurrence].1 ∈ cover
  · by_cases hright : I.edges[occurrence].2 ∈ cover
    · right
      right
      simp [selectedOccurrenceVertices,
        sourceEdgeForOccurrence_leftOccurrence hoccurrence, hleft, hright,
        selectedWidgetPath_leftOccurrence hoccurrence,
        selectedWidgetPath_rightOccurrence hoccurrence]
    · left
      simp [selectedOccurrenceVertices,
        sourceEdgeForOccurrence_leftOccurrence hoccurrence, hleft, hright,
        selectedWidgetPath_leftOccurrence hoccurrence]
  · have hright : I.edges[occurrence].2 ∈ cover := hcovered.resolve_left hleft
    right
    left
    simp [selectedOccurrenceVertices,
      sourceEdgeForOccurrence_leftOccurrence hoccurrence, hleft, hright,
      selectedWidgetPath_rightOccurrence hoccurrence]

theorem selectedOccurrenceVertices_nodup
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    (selectedOccurrenceVertices I cover occurrence).Nodup := by
  rcases selectedOccurrenceVertices_shape hoccurrence hcovered with
    hshape | hshape | hshape
  · rw [hshape]
    exact widgetLeftFullPath_isWidgetPath.1
  · rw [hshape]
    exact widgetRightFullPath_isWidgetPath.1
  · rw [hshape]
    exact widgetLeftPath_append_rightPath_nodup

theorem selectedOccurrenceVertices_length
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    (selectedOccurrenceVertices I cover occurrence).length =
      widgetVertexCount := by
  rcases selectedOccurrenceVertices_shape hoccurrence hcovered with
    hshape | hshape | hshape
  · simpa [hshape] using widgetLeftFullPath_length
  · simpa [hshape] using widgetRightFullPath_length
  · simpa [hshape] using widgetLeftPath_append_rightPath_length

theorem mem_selectedOccurrenceVertices_iff
    {I : CliqueInstance} {cover : Finset Nat} {occurrence localVertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcovered : I.edges[occurrence].1 ∈ cover ∨
      I.edges[occurrence].2 ∈ cover) :
    localVertex ∈ selectedOccurrenceVertices I cover occurrence ↔
      localVertex < widgetVertexCount := by
  rcases selectedOccurrenceVertices_shape hoccurrence hcovered with
    hshape | hshape | hshape
  · simpa [hshape] using mem_widgetLeftFullPath_iff localVertex
  · simpa [hshape] using mem_widgetRightFullPath_iff localVertex
  · rw [hshape, List.mem_append]
    exact mem_widgetLeft_or_rightPath_iff localVertex

end CLRS.Chapter34.HamiltonianCycleReduction
