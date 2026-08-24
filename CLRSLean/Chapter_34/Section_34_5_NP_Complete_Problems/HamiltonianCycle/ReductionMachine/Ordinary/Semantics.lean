import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Ordinary.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction

/-!
# VERTEX-COVER to HAM-CYCLE: edge-order semantic bridge
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary

open HamiltonianCycleReduction

theorem machineClrsInstance_adj_iff (I : VertexCoverInstance) (u v : Nat) :
    (machineClrsInstance I).Adj u v ↔
      (clrsHamiltonianInstance I).Adj u v := by
  rw [CliqueInstance.adj_iff, CliqueInstance.adj_iff]
  simp only [machineClrsInstance, clrsHamiltonianInstance]
  have hperm := machineClrsEdges_perm I
  constructor
  · rintro (⟨hlt, hedge⟩ | ⟨hlt, hedge⟩)
    · exact Or.inl ⟨hlt, hperm.subset hedge⟩
    · exact Or.inr ⟨hlt, hperm.subset hedge⟩
  · rintro (⟨hlt, hedge⟩ | ⟨hlt, hedge⟩)
    · exact Or.inl ⟨hlt, hperm.symm.subset hedge⟩
    · exact Or.inr ⟨hlt, hperm.symm.subset hedge⟩

private theorem pathAdjacent_iff (I : VertexCoverInstance)
    (vertices : List Nat) :
    (machineClrsInstance I).PathAdjacent vertices ↔
      (clrsHamiltonianInstance I).PathAdjacent vertices := by
  induction vertices using List.twoStepInduction with
  | nil => simp [CliqueInstance.PathAdjacent]
  | singleton vertex => simp [CliqueInstance.PathAdjacent]
  | cons_cons u v rest _ ih =>
      simp only [CliqueInstance.PathAdjacent, ih,
        machineClrsInstance_adj_iff]

private theorem cycleAdjacent_iff (I : VertexCoverInstance)
    (vertices : List Nat) :
    (machineClrsInstance I).CycleAdjacent vertices ↔
      (clrsHamiltonianInstance I).CycleAdjacent vertices := by
  cases vertices with
  | nil => rfl
  | cons first rest =>
      simp only [CliqueInstance.CycleAdjacent]
      rw [pathAdjacent_iff, machineClrsInstance_adj_iff]

theorem listRepresentsHamiltonianCycle_iff (I : VertexCoverInstance)
    (vertices : List Nat) :
    (machineClrsInstance I).ListRepresentsHamiltonianCycle vertices ↔
      (clrsHamiltonianInstance I).ListRepresentsHamiltonianCycle vertices := by
  simp only [CliqueInstance.ListRepresentsHamiltonianCycle]
  rw [show (machineClrsInstance I).vertexCount =
      (clrsHamiltonianInstance I).vertexCount from rfl]
  rw [cycleAdjacent_iff]

theorem hasHamiltonianCycle_iff (I : VertexCoverInstance) :
    (machineClrsInstance I).HasHamiltonianCycle ↔
      (clrsHamiltonianInstance I).HasHamiltonianCycle := by
  unfold CliqueInstance.HasHamiltonianCycle
  exact exists_congr fun vertices =>
    listRepresentsHamiltonianCycle_iff I vertices

theorem machineClrsInstance_wellFormed (I : VertexCoverInstance) :
    (machineClrsInstance I).WellFormed := by
  have hcanonical := clrsHamiltonianInstance_wellFormed I
  rcases hcanonical with ⟨htarget, hedges⟩
  constructor
  · simpa [machineClrsInstance, clrsHamiltonianInstance] using htarget
  · intro edge hedge
    apply hedges edge
    exact (machineClrsEdges_perm I).subset (by
      simpa [machineClrsInstance] using hedge)

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Ordinary
