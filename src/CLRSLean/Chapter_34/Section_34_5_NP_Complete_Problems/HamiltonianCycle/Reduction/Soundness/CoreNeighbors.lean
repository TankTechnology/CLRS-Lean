import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness.EdgeClassification

/-!
# Exact neighbors of the degree-two gadget core

The local vertices `1`, `4`, `7`, and `10` cannot be endpoints of any chain or
selector edge.  Consequently their two neighbors in the full reduction graph
are exactly their two vertical gadget neighbors.  These degree-two facts are
the forcing interface used by the finite gadget soundness argument.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem globalWidgetVertex_injective_of_local_lt
    {firstOccurrence firstLocal secondOccurrence secondLocal : Nat}
    (hfirst : firstLocal < widgetVertexCount)
    (hsecond : secondLocal < widgetVertexCount)
    (heq : globalWidgetVertex firstOccurrence firstLocal =
      globalWidgetVertex secondOccurrence secondLocal) :
    firstOccurrence = secondOccurrence ∧ firstLocal = secondLocal := by
  simp only [globalWidgetVertex, widgetVertexCount] at hfirst hsecond heq
  omega

theorem globalWidgetEdge_mem_clrsReductionEdges
    {I : CliqueInstance} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {localEdge : Nat × Nat} (hedge : localEdge ∈ widgetEdges) :
    (globalWidgetVertex occurrence localEdge.1,
      globalWidgetVertex occurrence localEdge.2) ∈ clrsReductionEdges I := by
  simp only [clrsReductionEdges, List.mem_append]
  left
  left
  left
  apply (mem_allGlobalWidgetEdges_iff).2
  exact ⟨occurrence, hoccurrence, localEdge, hedge, rfl⟩

theorem adj_globalWidgetVertex_of_widgetAdj
    (I : CliqueInstance) {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {firstLocal secondLocal : Nat}
    (hadj : widgetInstance.Adj firstLocal secondLocal) :
    (clrsHamiltonianInstance I).Adj
      (globalWidgetVertex occurrence firstLocal)
      (globalWidgetVertex occurrence secondLocal) := by
  rw [widgetInstance.adj_iff] at hadj
  rcases hadj with ⟨hlt, hedge⟩ | ⟨hlt, hedge⟩
  · apply CliqueInstance.adj_of_mem
    · simp [globalWidgetVertex]
      omega
    · exact globalWidgetEdge_mem_clrsReductionEdges hoccurrence hedge
  · rw [CliqueInstance.adj_comm]
    apply CliqueInstance.adj_of_mem
    · simp [globalWidgetVertex]
      omega
    · exact globalWidgetEdge_mem_clrsReductionEdges hoccurrence hedge

/-- An internal non-port vertex sees only the neighbors of the corresponding
local gadget vertex. -/
theorem adj_globalWidgetInternalVertex_iff
    {I : CliqueInstance} {occurrence localVertex vertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hinternal : IsWidgetInternalVertex localVertex) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence localVertex) vertex ↔
      ∃ localNeighbor,
        widgetInstance.Adj localVertex localNeighbor ∧
        vertex = globalWidgetVertex occurrence localNeighbor := by
  constructor
  · intro hadj
    rcases endpoint_of_adj hadj with ⟨edge, hedge, hends⟩
    change edge ∈ clrsReductionEdges I at hedge
    unfold clrsReductionEdges at hedge
    rcases List.mem_append.mp hedge with hedge | hedgeClique
    · rcases List.mem_append.mp hedge with hedge | hedgeSelector
      · rcases List.mem_append.mp hedge with hedgeWidget | hedgeChain
        · rcases (mem_allGlobalWidgetEdges_iff).mp hedgeWidget with
            ⟨otherOccurrence, hotherOccurrence, localEdge, hlocalEdge, rfl⟩
          have hlocalWellFormed := widgetInstance_wellFormed.2 _ hlocalEdge
          have hfirstLocal : localEdge.1 < widgetVertexCount := by
            change localEdge.1 < widgetInstance.vertexCount
            omega
          have hsecondLocal : localEdge.2 < widgetVertexCount := by
            exact hlocalWellFormed.2
          rcases hends with hends | hends
          · have hident := globalWidgetVertex_injective_of_local_lt
                (widgetInternalVertex_lt hinternal) hfirstLocal hends.1
            rw [← hident.1] at hends
            refine ⟨localEdge.2, ?_, hends.2⟩
            rw [hident.2]
            exact CliqueInstance.adj_of_mem widgetInstance
              hlocalWellFormed.1 hlocalEdge
          · have hident := globalWidgetVertex_injective_of_local_lt
                (widgetInternalVertex_lt hinternal) hsecondLocal hends.1
            rw [← hident.1] at hends
            refine ⟨localEdge.1, ?_, hends.2⟩
            rw [hident.2]
            exact (widgetInstance.adj_comm _ _).2
              (CliqueInstance.adj_of_mem widgetInstance
                hlocalWellFormed.1 hlocalEdge)
        · have hnot := globalWidgetInternalVertex_not_endpoint_incidenceChainEdge
              hoccurrence hinternal hedgeChain
          rcases hends with hends | hends
          · exact (hnot.1 hends.1).elim
          · exact (hnot.2 hends.1).elim
      · have hnot := globalWidgetInternalVertex_not_endpoint_selectorEndpointEdge
            hoccurrence hinternal hedgeSelector
        rcases hends with hends | hends
        · exact (hnot.1 hends.1).elim
        · exact (hnot.2 hends.1).elim
    · have hnot := globalWidgetInternalVertex_not_endpoint_selectorCliqueEdge
          hoccurrence hinternal hedgeClique
      rcases hends with hends | hends
      · exact (hnot.1 hends.1).elim
      · exact (hnot.2 hends.1).elim
  · rintro ⟨localNeighbor, hadj, rfl⟩
    exact adj_globalWidgetVertex_of_widgetAdj I hoccurrence hadj

/-- Backward-compatible degree-two-core specialization. -/
theorem adj_globalWidgetCoreVertex_iff
    {I : CliqueInstance} {occurrence localVertex vertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hcore : IsWidgetCoreVertex localVertex) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence localVertex) vertex ↔
      ∃ localNeighbor,
        widgetInstance.Adj localVertex localNeighbor ∧
        vertex = globalWidgetVertex occurrence localNeighbor :=
  adj_globalWidgetInternalVertex_iff hoccurrence (Or.inl hcore)

theorem widgetInstance_adj_one_iff (localNeighbor : Nat) :
    widgetInstance.Adj 1 localNeighbor ↔
      localNeighbor = 0 ∨ localNeighbor = 2 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_four_iff (localNeighbor : Nat) :
    widgetInstance.Adj 4 localNeighbor ↔
      localNeighbor = 3 ∨ localNeighbor = 5 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_seven_iff (localNeighbor : Nat) :
    widgetInstance.Adj 7 localNeighbor ↔
      localNeighbor = 6 ∨ localNeighbor = 8 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_ten_iff (localNeighbor : Nat) :
    widgetInstance.Adj 10 localNeighbor ↔
      localNeighbor = 9 ∨ localNeighbor = 11 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_two_iff (localNeighbor : Nat) :
    widgetInstance.Adj 2 localNeighbor ↔
      localNeighbor = 1 ∨ localNeighbor = 3 ∨ localNeighbor = 6 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_three_iff (localNeighbor : Nat) :
    widgetInstance.Adj 3 localNeighbor ↔
      localNeighbor = 2 ∨ localNeighbor = 4 ∨ localNeighbor = 11 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_eight_iff (localNeighbor : Nat) :
    widgetInstance.Adj 8 localNeighbor ↔
      localNeighbor = 7 ∨ localNeighbor = 9 ∨ localNeighbor = 0 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem widgetInstance_adj_nine_iff (localNeighbor : Nat) :
    widgetInstance.Adj 9 localNeighbor ↔
      localNeighbor = 8 ∨ localNeighbor = 10 ∨ localNeighbor = 5 := by
  simp [widgetInstance, CliqueInstance.Adj, widgetEdges]
  split <;> omega

theorem adj_globalWidgetInternalVertex_iff_three
    {I : CliqueInstance} {occurrence localVertex first second third vertex : Nat}
    (hoccurrence : occurrence < I.edges.length)
    (hinternal : IsWidgetInternalVertex localVertex)
    (hadj : ∀ localNeighbor,
      widgetInstance.Adj localVertex localNeighbor ↔
        localNeighbor = first ∨ localNeighbor = second ∨
          localNeighbor = third) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence localVertex) vertex ↔
      vertex = globalWidgetVertex occurrence first ∨
      vertex = globalWidgetVertex occurrence second ∨
      vertex = globalWidgetVertex occurrence third := by
  rw [adj_globalWidgetInternalVertex_iff hoccurrence hinternal]
  constructor
  · rintro ⟨localNeighbor, hlocalAdj, rfl⟩
    rcases (hadj localNeighbor).mp hlocalAdj with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨first, (hadj first).2 (Or.inl rfl), rfl⟩
    · exact ⟨second, (hadj second).2 (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨third, (hadj third).2 (Or.inr (Or.inr rfl)), rfl⟩

theorem adj_globalWidgetVertex_two_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 2) vertex ↔
      vertex = globalWidgetVertex occurrence 1 ∨
      vertex = globalWidgetVertex occurrence 3 ∨
      vertex = globalWidgetVertex occurrence 6 :=
  adj_globalWidgetInternalVertex_iff_three hoccurrence
    (Or.inr (Or.inl rfl)) widgetInstance_adj_two_iff

theorem adj_globalWidgetVertex_three_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 3) vertex ↔
      vertex = globalWidgetVertex occurrence 2 ∨
      vertex = globalWidgetVertex occurrence 4 ∨
      vertex = globalWidgetVertex occurrence 11 :=
  adj_globalWidgetInternalVertex_iff_three hoccurrence
    (Or.inr (Or.inr (Or.inl rfl))) widgetInstance_adj_three_iff

theorem adj_globalWidgetVertex_eight_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 8) vertex ↔
      vertex = globalWidgetVertex occurrence 7 ∨
      vertex = globalWidgetVertex occurrence 9 ∨
      vertex = globalWidgetVertex occurrence 0 :=
  adj_globalWidgetInternalVertex_iff_three hoccurrence
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) widgetInstance_adj_eight_iff

theorem adj_globalWidgetVertex_nine_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 9) vertex ↔
      vertex = globalWidgetVertex occurrence 8 ∨
      vertex = globalWidgetVertex occurrence 10 ∨
      vertex = globalWidgetVertex occurrence 5 :=
  adj_globalWidgetInternalVertex_iff_three hoccurrence
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) widgetInstance_adj_nine_iff

theorem adj_globalWidgetVertex_one_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 1) vertex ↔
      vertex = globalWidgetVertex occurrence 0 ∨
      vertex = globalWidgetVertex occurrence 2 := by
  rw [adj_globalWidgetCoreVertex_iff hoccurrence (Or.inl rfl)]
  constructor
  · rintro ⟨localNeighbor, hadj, rfl⟩
    rcases (widgetInstance_adj_one_iff localNeighbor).mp hadj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, (widgetInstance_adj_one_iff 0).2 (Or.inl rfl), rfl⟩
    · exact ⟨2, (widgetInstance_adj_one_iff 2).2 (Or.inr rfl), rfl⟩

theorem adj_globalWidgetVertex_four_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 4) vertex ↔
      vertex = globalWidgetVertex occurrence 3 ∨
      vertex = globalWidgetVertex occurrence 5 := by
  rw [adj_globalWidgetCoreVertex_iff hoccurrence (Or.inr (Or.inl rfl))]
  constructor
  · rintro ⟨localNeighbor, hadj, rfl⟩
    rcases (widgetInstance_adj_four_iff localNeighbor).mp hadj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨3, (widgetInstance_adj_four_iff 3).2 (Or.inl rfl), rfl⟩
    · exact ⟨5, (widgetInstance_adj_four_iff 5).2 (Or.inr rfl), rfl⟩

theorem adj_globalWidgetVertex_seven_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 7) vertex ↔
      vertex = globalWidgetVertex occurrence 6 ∨
      vertex = globalWidgetVertex occurrence 8 := by
  rw [adj_globalWidgetCoreVertex_iff hoccurrence
    (Or.inr (Or.inr (Or.inl rfl)))]
  constructor
  · rintro ⟨localNeighbor, hadj, rfl⟩
    rcases (widgetInstance_adj_seven_iff localNeighbor).mp hadj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨6, (widgetInstance_adj_seven_iff 6).2 (Or.inl rfl), rfl⟩
    · exact ⟨8, (widgetInstance_adj_seven_iff 8).2 (Or.inr rfl), rfl⟩

theorem adj_globalWidgetVertex_ten_iff
    {I : CliqueInstance} {occurrence vertex : Nat}
    (hoccurrence : occurrence < I.edges.length) :
    (clrsHamiltonianInstance I).Adj
        (globalWidgetVertex occurrence 10) vertex ↔
      vertex = globalWidgetVertex occurrence 9 ∨
      vertex = globalWidgetVertex occurrence 11 := by
  rw [adj_globalWidgetCoreVertex_iff hoccurrence
    (Or.inr (Or.inr (Or.inr rfl)))]
  constructor
  · rintro ⟨localNeighbor, hadj, rfl⟩
    rcases (widgetInstance_adj_ten_iff localNeighbor).mp hadj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨9, (widgetInstance_adj_ten_iff 9).2 (Or.inl rfl), rfl⟩
    · exact ⟨11, (widgetInstance_adj_ten_iff 11).2 (Or.inr rfl), rfl⟩

end CLRS.Chapter34.HamiltonianCycleReduction
