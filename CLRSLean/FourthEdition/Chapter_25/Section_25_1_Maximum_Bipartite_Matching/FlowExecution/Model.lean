import CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching

/-!
# Cost model for the §25.1 bipartite-flow execution

The selected representation is an adjacency-list representation of the
support of the unit-capacity flow network.  Its forward arcs are the
source-to-left arcs, the original bipartite edges, and the right-to-sink
arcs.  Residual BFS scans at most both orientations of every support arc.
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

/-- Adjacency-list work charged to one complete residual BFS. -/
def adjacencyBFSWork (G : BipartiteGraph V) : ℕ :=
  flowVertexCount V + 2 * flowArcCount G

/-- Work charged to updating a simple augmenting path. -/
def pathUpdateWork (_G : BipartiteGraph V) : ℕ :=
  flowVertexCount V

/-- Total work budget charged to one BFS augmentation attempt. -/
def augmentationAttemptWork (G : BipartiteGraph V) : ℕ :=
  adjacencyBFSWork G + pathUpdateWork G

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

/-- One residual BFS plus one simple-path update is linear in the number of
support arcs of the constructed flow network. -/
theorem augmentationAttemptWork_le (G : BipartiteGraph V) :
    augmentationAttemptWork G ≤ 4 * (flowArcCount G + 1) := by
  simp only [augmentationAttemptWork, adjacencyBFSWork, pathUpdateWork,
    flowVertexCount_eq]
  rw [flowArcCount_eq]
  omega

end Matchings
end CLRS
