import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.CertificateCoverage

/-!
# Completeness of the VERTEX-COVER to HAM-CYCLE construction

All certificate obligations are assembled here: global vertex coverage from
`CertificateCoverage`, adjacency from `CertificateAdjacency`, and the total
reduction's two degenerate branches from `Construction.Instance`.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

theorem coverHamiltonianCertificate_representsHamiltonianCycle
    {I : CliqueInstance} {cover : Finset Nat}
    (hwellFormed : I.WellFormed) (hcard : cover.card ≤ I.targetSize)
    (hcover : I.IsVertexCover cover) (hedges : I.edges ≠ []) :
    (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle
      (coverHamiltonianCertificate I cover) := by
  refine ⟨?_,
    coverHamiltonianCertificate_nodup hwellFormed hcard hcover,
    coverHamiltonianCertificate_length hwellFormed hcard hcover,
    ?_, coverHamiltonianCertificate_cycleAdjacent hcover hcard hedges⟩
  · have hedgeCount : 0 < I.edges.length := List.length_pos_of_ne_nil hedges
    rw [clrsHamiltonianInstance_vertexCount]
    simp only [widgetVertexCount]
    omega
  · intro vertex hvertex
    exact coverHamiltonianCertificate_vertex_lt
      hwellFormed hcard hcover hvertex

theorem clrsHamiltonianInstance_hasHamiltonianCycle_of_hasVertexCover
    {I : CliqueInstance} (hwellFormed : I.WellFormed)
    (hedges : I.edges ≠ []) (hyes : I.HasVertexCover) :
    (clrsHamiltonianInstance I).HasHamiltonianCycle := by
  rcases hyes with ⟨cover, hcard, hcover⟩
  exact ⟨coverHamiltonianCertificate I cover,
    coverHamiltonianCertificate_representsHamiltonianCycle
      hwellFormed hcard hcover hedges⟩

theorem no_vertexCover_of_edges_ne_nil_targetSize_zero
    {I : CliqueInstance} (hedges : I.edges ≠ []) (htarget : I.targetSize = 0) :
    ¬ I.HasVertexCover := by
  rintro ⟨cover, hcard, hcover⟩
  have hcoverEmpty : cover = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  obtain ⟨edge, hedge⟩ := List.exists_mem_of_ne_nil I.edges hedges
  have hcovered := I.edge_covered_of_isVertexCover hcover hedge
  simpa [hcoverEmpty] using hcovered

/-- Completeness direction of the total typed CLRS reduction. -/
theorem vertexCoverToHamiltonianInstance_complete
    {I : VertexCoverInstance} (hwellFormed : I.WellFormed) :
    I.HasVertexCover →
      (vertexCoverToHamiltonianInstance I).HasHamiltonianCycle := by
  intro hyes
  by_cases hedges : I.edges = []
  · rw [vertexCoverToHamiltonianInstance, if_pos hedges]
    exact canonicalHamiltonianYesInstance_hasHamiltonianCycle
  · by_cases htarget : I.targetSize = 0
    · exact (no_vertexCover_of_edges_ne_nil_targetSize_zero hedges htarget hyes).elim
    · rw [vertexCoverToHamiltonianInstance, if_neg hedges, if_neg htarget]
      exact clrsHamiltonianInstance_hasHamiltonianCycle_of_hasVertexCover
        hwellFormed hedges hyes

end CLRS.Chapter34.HamiltonianCycleReduction
