import CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching

/-!
# Cost vocabulary for the adjacency-list §25.1 execution

These definitions state the textbook adjacency-list budget vocabulary for the
support of the unit-capacity flow network.  The legacy `residualBFS` still
enumerates the finite vertex universe; `CostedSupportBFS` and `CostedRun`
provide the separate support-indexed execution and its attached `O(VE)`
theorem.
-/

namespace CLRS
namespace Matchings

open Finset Classical
open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of forward support arcs in the bipartite flow network. -/
def flowArcCount (G : BipartiteGraph V) : ℕ :=
  G.L.card + G.E.card + G.R.card

/-- Number of vertices in the flow network, including source and sink. -/
def flowVertexCount (V : Type*) [Fintype V] : ℕ :=
  Fintype.card (V ⊕ Bool)

/-- Coarse adjacency-list specification budget for one residual BFS. -/
def adjacencyBFSBudget (G : BipartiteGraph V) : ℕ :=
  flowVertexCount V + 2 * flowArcCount G

/-- Coarse specification budget for updating a simple augmenting path. -/
def pathUpdateBudget (_G : BipartiteGraph V) : ℕ :=
  flowVertexCount V

/-- Coarse specification budget for one adjacency-list augmentation attempt. -/
def augmentationAttemptBudget (G : BipartiteGraph V) : ℕ :=
  adjacencyBFSBudget G + pathUpdateBudget G

/-- The two bipartition sizes add up to the number of graph vertices. -/
theorem partition_card (G : BipartiteGraph V) :
    G.L.card + G.R.card = Fintype.card V := by
  have hd : Disjoint G.L G.R :=
    Finset.disjoint_iff_inter_eq_empty.mpr G.h_disjoint
  rw [← Finset.card_union_of_disjoint hd, G.h_cover]
  simp

/-- The constructed network has one support arc per graph vertex plus one
arc per graph edge. -/
theorem flowArcCount_eq (G : BipartiteGraph V) :
    flowArcCount G = Fintype.card V + G.E.card := by
  unfold flowArcCount
  have h := partition_card G
  omega

omit [DecidableEq V] in
@[simp]
theorem flowVertexCount_eq :
    flowVertexCount V = Fintype.card V + 2 := by
  simp [flowVertexCount]

/-- The number of possible matching augmentations is at most `|V|`. -/
theorem left_card_le_vertex_card (G : BipartiteGraph V) :
    G.L.card ≤ Fintype.card V := by
  exact Finset.card_le_card (Finset.subset_univ G.L)

/-- The target per-attempt budget is linear in the number of support arcs.

This arithmetic lemma is a coarse specification bound; it is not a cost
theorem about the legacy all-vertices `residualBFS`.  The attached execution
theorem is `costedMatchingRun_work_le_product`. -/
theorem augmentationAttemptBudget_le (G : BipartiteGraph V) :
    augmentationAttemptBudget G ≤ 4 * (flowArcCount G + 1) := by
  simp only [augmentationAttemptBudget, adjacencyBFSBudget, pathUpdateBudget,
    flowVertexCount_eq]
  rw [flowArcCount_eq]
  omega

end Matchings
end CLRS
