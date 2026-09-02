import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.GadgetClassification

/-!
# Reading a source cover from gadget traversals

A source vertex is selected when the Hamiltonian cycle uses the side of one
of its incident gadgets.  The three-way gadget classification immediately
shows that every source edge has at least one selected endpoint.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

def CycleUsesIncidentSide
    (vertices : List Nat) (ref : IncidentOccurrence) : Prop :=
  if ref.rightSide then
    UsesWidgetSplitTraversal vertices ref.occurrence ∨
      UsesWidgetRightFullTraversal vertices ref.occurrence
  else
    UsesWidgetSplitTraversal vertices ref.occurrence ∨
      UsesWidgetLeftFullTraversal vertices ref.occurrence

def CycleSelectsSourceVertex
    (I : CliqueInstance) (vertices : List Nat) (u : Nat) : Prop :=
  ∃ ref ∈ incidentOccurrences I u, CycleUsesIncidentSide vertices ref

noncomputable def cycleSelectedSourceVertices
    (I : CliqueInstance) (vertices : List Nat) : Finset Nat := by
  classical
  exact (Finset.range I.vertexCount).filter
    (CycleSelectsSourceVertex I vertices)

theorem mem_cycleSelectedSourceVertices_iff
    {I : CliqueInstance} {vertices : List Nat} {u : Nat} :
    u ∈ cycleSelectedSourceVertices I vertices ↔
      u < I.vertexCount ∧ CycleSelectsSourceVertex I vertices u := by
  classical
  simp [cycleSelectedSourceVertices]

theorem cycleUsesIncidentSide_left
    {vertices : List Nat} {occurrence : Nat}
    (htraversal : UsesWidgetSplitTraversal vertices occurrence ∨
      UsesWidgetLeftFullTraversal vertices occurrence) :
    CycleUsesIncidentSide vertices
      { occurrence := occurrence, rightSide := false } := by
  simpa [CycleUsesIncidentSide] using htraversal

theorem cycleUsesIncidentSide_right
    {vertices : List Nat} {occurrence : Nat}
    (htraversal : UsesWidgetSplitTraversal vertices occurrence ∨
      UsesWidgetRightFullTraversal vertices occurrence) :
    CycleUsesIncidentSide vertices
      { occurrence := occurrence, rightSide := true } := by
  simpa [CycleUsesIncidentSide] using htraversal

theorem cycleSelectedSourceVertices_isVertexCover
    {I : CliqueInstance} (hwellFormed : I.WellFormed)
    {vertices : List Nat}
    (hcycle : (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      vertices)
    (htarget : 0 < I.targetSize) :
    I.IsVertexCover (cycleSelectedSourceVertices I vertices) := by
  constructor
  · intro u hu
    exact (mem_cycleSelectedSourceVertices_iff.mp hu).1
  · intro edge hedge
    obtain ⟨occurrence, hoccurrence, hedgeEq⟩ := List.getElem_of_mem hedge
    subst edge
    have hedgeProperties := hwellFormed.2 I.edges[occurrence]
      (List.getElem_mem hoccurrence)
    have hleftBound : I.edges[occurrence].1 < I.vertexCount := by
      omega
    have hrightBound : I.edges[occurrence].2 < I.vertexCount :=
      hedgeProperties.2
    have hleftRef :
        ({ occurrence := occurrence, rightSide := false } :
          IncidentOccurrence) ∈ incidentOccurrences I I.edges[occurrence].1 :=
      leftIncidentOccurrence_mem hoccurrence rfl
    have hrightRef :
        ({ occurrence := occurrence, rightSide := true } :
          IncidentOccurrence) ∈ incidentOccurrences I I.edges[occurrence].2 :=
      rightIncidentOccurrence_mem hoccurrence (by omega) rfl
    rcases cycle_uses_allowed_widget_traversal hcycle htarget hoccurrence with
      hsplit | hleftFull | hrightFull
    · left
      apply mem_cycleSelectedSourceVertices_iff.mpr
      exact ⟨hleftBound,
        ⟨{ occurrence := occurrence, rightSide := false }, hleftRef,
          cycleUsesIncidentSide_left (Or.inl hsplit)⟩⟩
    · left
      apply mem_cycleSelectedSourceVertices_iff.mpr
      exact ⟨hleftBound,
        ⟨{ occurrence := occurrence, rightSide := false }, hleftRef,
          cycleUsesIncidentSide_left (Or.inr hleftFull)⟩⟩
    · right
      apply mem_cycleSelectedSourceVertices_iff.mpr
      exact ⟨hrightBound,
        ⟨{ occurrence := occurrence, rightSide := true }, hrightRef,
          cycleUsesIncidentSide_right (Or.inr hrightFull)⟩⟩

end CLRS.Chapter34.HamiltonianCycleReduction
