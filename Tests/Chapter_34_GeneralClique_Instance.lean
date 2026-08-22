import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Instance

namespace CLRS.Chapter34

private def triangle : CliqueInstance where
  vertexCount := 3
  targetSize := 3
  edges := [(0, 1), (0, 2), (1, 2)]

private def path : CliqueInstance where
  vertexCount := 3
  targetSize := 3
  edges := [(0, 1), (1, 2)]

private def reversedEdge : CliqueInstance where
  vertexCount := 2
  targetSize := 2
  edges := [(1, 0)]

example : triangle.WellFormed := by native_decide

example : ¬ reversedEdge.WellFormed := by native_decide

example : triangle.Adj 0 2 := by native_decide

example : triangle.Adj 2 0 := by native_decide

example : ¬ path.Adj 0 2 := by native_decide

example : triangle.HasClique := by
  refine ⟨{0, 1, 2}, by decide, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> decide
  · intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl <;>
      simp_all [triangle, CliqueInstance.Adj]

example : ¬ path.HasClique := by
  rintro ⟨vertices, hcard, hbound, hadj⟩
  have hsubset : vertices ⊆ Finset.range 3 := by
    intro v hv
    exact Finset.mem_range.mpr (by simpa [path] using hbound v hv)
  have hcard' : vertices.card = 3 := by
    simpa [path] using hcard
  have hvertices : vertices = Finset.range 3 := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simp [hcard']
  have hzero : 0 ∈ vertices := by simp [hvertices]
  have htwo : 2 ∈ vertices := by simp [hvertices]
  exact (by native_decide : ¬ path.Adj 0 2) (hadj 0 hzero 2 htwo (by decide))

end CLRS.Chapter34
