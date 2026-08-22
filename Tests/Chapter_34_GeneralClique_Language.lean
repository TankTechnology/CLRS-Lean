import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Language

namespace CLRS.Chapter34

private def oneEdgeClique : CliqueInstance where
  vertexCount := 2
  targetSize := 2
  edges := [(0, 1)]

private def duplicateEdgeInstance : CliqueInstance where
  vertexCount := 2
  targetSize := 2
  edges := [(0, 1), (0, 1)]

private theorem oneEdgeClique_hasClique : oneEdgeClique.HasClique := by
  refine ⟨{0, 1}, by decide, ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> decide
  · intro u hu v hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;>
      rcases hv with rfl | rfl <;>
      simp_all [oneEdgeClique, CliqueInstance.Adj]

example : encodeCliqueInstance oneEdgeClique ∈ GeneralCLIQUE := by
  exact (encodeCliqueInstance_mem_generalCLIQUE_iff oneEdgeClique).2
    ⟨by native_decide, oneEdgeClique_hasClique⟩

example : encodeCliqueInstance duplicateEdgeInstance ∉ GeneralCLIQUE := by
  rw [encodeCliqueInstance_mem_generalCLIQUE_iff]
  exact fun h => (by native_decide : ¬ duplicateEdgeInstance.WellFormed) h.1

example : ([.certificateMark] : List CliqueSym) ∉ GeneralCLIQUE := by
  simp [GeneralCLIQUE, decodeCliqueInstance]

end CLRS.Chapter34
