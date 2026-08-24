import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.Edges
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.CycleInterface
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Instance

/-!
# Typed target instance for VERTEX-COVER to HAM-CYCLE

The ordinary CLRS construction is used when the source has an edge and a
positive target.  The two degenerate cases are mapped to fixed three-vertex
yes/no instances.  This keeps the reduction total while preserving the
project's convention that a Hamiltonian cycle has at least three vertices.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- A fixed triangle yes-instance. -/
def canonicalHamiltonianYesInstance : HamiltonianCycleInstance where
  vertexCount := 3
  targetSize := 3
  edges := [(0, 1), (0, 2), (1, 2)]

/-- A fixed three-vertex path no-instance. -/
def canonicalHamiltonianNoInstance : HamiltonianCycleInstance where
  vertexCount := 3
  targetSize := 3
  edges := [(0, 1), (1, 2)]

/-- The nondegenerate CLRS graph: twelve vertices per edge occurrence followed
by the encoded number of selector vertices. -/
def clrsHamiltonianInstance (I : VertexCoverInstance) :
    HamiltonianCycleInstance where
  vertexCount := selectorBase I.edges.length + I.targetSize
  targetSize := selectorBase I.edges.length + I.targetSize
  edges := clrsReductionEdges I

/-- Total typed reduction.  Edgeless graphs are always yes-instances of the
at-most-`k` VERTEX-COVER language; nonempty graphs with `k = 0` are no-instances. -/
def vertexCoverToHamiltonianInstance (I : VertexCoverInstance) :
    HamiltonianCycleInstance :=
  if I.edges = [] then canonicalHamiltonianYesInstance
  else if I.targetSize = 0 then canonicalHamiltonianNoInstance
  else clrsHamiltonianInstance I

theorem canonicalHamiltonianYesInstance_wellFormed :
    canonicalHamiltonianYesInstance.WellFormed := by
  decide

theorem canonicalHamiltonianNoInstance_wellFormed :
    canonicalHamiltonianNoInstance.WellFormed := by
  decide

theorem canonicalHamiltonianYesInstance_hasHamiltonianCycle :
    canonicalHamiltonianYesInstance.HasHamiltonianCycle := by
  refine ⟨0 :: 1 :: 2 :: [], ?_⟩
  decide

theorem not_canonicalHamiltonianNoInstance_hasHamiltonianCycle :
    ¬canonicalHamiltonianNoInstance.HasHamiltonianCycle := by
  rintro ⟨vertices, hvertices⟩
  rcases hvertices with ⟨hthree, hnodup, hlength, hbound, hcycle⟩
  have hmem0 := CliqueInstance.mem_of_lt_of_full_cycle_list hnodup hlength hbound
    (show 0 < canonicalHamiltonianNoInstance.vertexCount by decide)
  have hnext := canonicalHamiltonianNoInstance.adj_next_of_cycleAdjacent
    hnodup hcycle hmem0
  have hprev := canonicalHamiltonianNoInstance.adj_prev_of_cycleAdjacent
    hnodup hcycle hmem0
  have hnextEq : vertices.next 0 hmem0 = 1 := by
    have h := (show 0 < vertices.next 0 hmem0 ∧
        vertices.next 0 hmem0 = 1 by
      simpa [canonicalHamiltonianNoInstance, CliqueInstance.Adj] using hnext)
    exact h.2
  have hprevEq : vertices.prev 0 hmem0 = 1 := by
    have h := (show 0 < vertices.prev 0 hmem0 ∧
        vertices.prev 0 hmem0 = 1 by
      simpa [canonicalHamiltonianNoInstance, CliqueInstance.Adj] using hprev)
    exact h.2
  exact (CliqueInstance.next_ne_prev_of_three_le_length hnodup
    (by simpa [hlength] using hthree) hmem0) (hnextEq.trans hprevEq.symm)

theorem clrsHamiltonianInstance_vertexCount (I : VertexCoverInstance) :
    (clrsHamiltonianInstance I).vertexCount =
      widgetVertexCount * I.edges.length + I.targetSize := by
  rfl

theorem clrsHamiltonianInstance_target_eq_vertexCount
    (I : VertexCoverInstance) :
    (clrsHamiltonianInstance I).targetSize =
      (clrsHamiltonianInstance I).vertexCount := by
  rfl

end CLRS.Chapter34.HamiltonianCycleReduction
