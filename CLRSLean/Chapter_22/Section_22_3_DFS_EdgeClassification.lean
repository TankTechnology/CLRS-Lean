import Mathlib
import CLRSLean.Chapter_22.Section_22_3_DFS_SCC

/-! # DFS theory: edge classification

This file classifies every directed graph edge relative to the final DFS
parent forest.  Self-loops count as back edges, following CLRS.  Besides the
four structural predicates, it proves uniqueness and the standard timestamp
characterizations of tree/forward, back, and cross edges.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- A tree edge is the edge that installed the target's final parent pointer. -/
def IsDFSTreeEdge (u v : V) : Prop :=
  G.Adj u v ∧ (G.dfs).parent v = some u

/-- A back edge points to an ancestor in the final DFS forest.  Because ancestry
is reflexive, a self-loop is a back edge. -/
def IsDFSBackEdge (u v : V) : Prop :=
  G.Adj u v ∧ IsDFSAncestor (G.dfs) v u

/-- A forward edge is a non-tree edge from a vertex to a proper descendant. -/
def IsDFSForwardEdge (u v : V) : Prop :=
  G.Adj u v ∧ u ≠ v ∧ IsDFSAncestor (G.dfs) u v ∧
    (G.dfs).parent v ≠ some u

/-- A cross edge joins vertices that are unrelated by DFS ancestry. -/
def IsDFSCrossEdge (u v : V) : Prop :=
  G.Adj u v ∧ ¬IsDFSAncestor (G.dfs) u v ∧
    ¬IsDFSAncestor (G.dfs) v u

/-- An undirected tree edge has a parent pointer in either orientation. -/
def IsDFSUndirectedTreeEdge (u v : V) : Prop :=
  G.IsDFSTreeEdge u v ∨ G.IsDFSTreeEdge v u

/-- An undirected back edge joins an ancestor and descendant in either
orientation. -/
def IsDFSUndirectedBackEdge (u v : V) : Prop :=
  G.IsDFSBackEdge u v ∨ G.IsDFSBackEdge v u

/-- The four CLRS edge classes for a directed DFS forest. -/
inductive DFSEdgeKind where
  | tree
  | back
  | forward
  | cross
  deriving DecidableEq, Repr

/-- A graph edge has a specified DFS edge kind. -/
def HasDFSEdgeKind (kind : DFSEdgeKind) (u v : V) : Prop :=
  match kind with
  | .tree => G.IsDFSTreeEdge u v
  | .back => G.IsDFSBackEdge u v
  | .forward => G.IsDFSForwardEdge u v
  | .cross => G.IsDFSCrossEdge u v

/-- Every graph self-loop is a DFS back edge. -/
theorem dfs_self_loop_is_back {u : V} (hloop : G.Adj u u) :
    G.IsDFSBackEdge u u :=
  ⟨hloop, IsDFSAncestor.refl (G.dfs) u⟩

/-- Mutual DFS ancestry in the final parent forest implies equality. -/
theorem IsDFSAncestor.antisymm_dfs {u v : V}
    (huv : IsDFSAncestor (G.dfs) u v)
    (hvu : IsDFSAncestor (G.dfs) v u) : u = v := by
  rcases IsDFSAncestor.eq_or_discovery_lt G huv with huv_eq | huv_lt
  · exact huv_eq
  rcases IsDFSAncestor.eq_or_discovery_lt G hvu with hvu_eq | hvu_lt
  · exact hvu_eq.symm
  · omega

/-- A final parent pointer never points from a vertex to itself. -/
theorem dfs_parent_ne {u v : V} (hparent : (G.dfs).parent v = some u) :
    u ≠ v := by
  intro h
  subst v
  have hlt := dfs_parent_discovery_lt G hparent
  omega

/-- A final DFS tree edge cannot also be a back edge. -/
theorem dfs_tree_edge_not_back {u v : V}
    (htree : G.IsDFSTreeEdge u v) : ¬G.IsDFSBackEdge u v := by
  intro hback
  have huv : IsDFSAncestor (G.dfs) u v := IsDFSAncestor.single htree.2
  have huv_eq := IsDFSAncestor.antisymm_dfs G huv hback.2
  exact (dfs_parent_ne G htree.2) huv_eq

/-- A tree edge cannot also be a forward edge. -/
theorem dfs_tree_edge_not_forward {u v : V}
    (htree : G.IsDFSTreeEdge u v) : ¬G.IsDFSForwardEdge u v := by
  intro hforward
  exact hforward.2.2.2 htree.2

/-- A tree edge cannot also be a cross edge. -/
theorem dfs_tree_edge_not_cross {u v : V}
    (htree : G.IsDFSTreeEdge u v) : ¬G.IsDFSCrossEdge u v := by
  intro hcross
  exact hcross.2.1 (IsDFSAncestor.single htree.2)

/-- A forward edge cannot also be a back edge. -/
theorem dfs_forward_edge_not_back {u v : V}
    (hforward : G.IsDFSForwardEdge u v) : ¬G.IsDFSBackEdge u v := by
  intro hback
  have huv_eq := IsDFSAncestor.antisymm_dfs G hforward.2.2.1 hback.2
  exact hforward.2.1 huv_eq

/-- A back edge cannot also be a cross edge. -/
theorem dfs_back_edge_not_cross {u v : V}
    (hback : G.IsDFSBackEdge u v) : ¬G.IsDFSCrossEdge u v := by
  intro hcross
  exact hcross.2.2 hback.2

/-- A forward edge cannot also be a cross edge. -/
theorem dfs_forward_edge_not_cross {u v : V}
    (hforward : G.IsDFSForwardEdge u v) : ¬G.IsDFSCrossEdge u v := by
  intro hcross
  exact hcross.2.1 hforward.2.2.1

/-- Every graph edge belongs to at least one DFS edge class. -/
theorem dfs_edge_classification {u v : V} (hadj : G.Adj u v) :
    G.IsDFSTreeEdge u v ∨ G.IsDFSBackEdge u v ∨
      G.IsDFSForwardEdge u v ∨ G.IsDFSCrossEdge u v := by
  by_cases hparent : (G.dfs).parent v = some u
  · exact Or.inl ⟨hadj, hparent⟩
  by_cases hback : IsDFSAncestor (G.dfs) v u
  · exact Or.inr (Or.inl ⟨hadj, hback⟩)
  by_cases hforward : IsDFSAncestor (G.dfs) u v
  · have hne : u ≠ v := by
      intro h
      subst v
      exact hback (IsDFSAncestor.refl (G.dfs) u)
    exact Or.inr (Or.inr (Or.inl ⟨hadj, hne, hforward, hparent⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hadj, hforward, hback⟩))

/-- Every graph edge has exactly one DFS edge kind. -/
theorem dfs_edge_classification_unique {u v : V} (hadj : G.Adj u v) :
    ∃! kind, G.HasDFSEdgeKind kind u v := by
  rcases dfs_edge_classification G hadj with htree | hback | hforward | hcross
  · refine ⟨.tree, htree, ?_⟩
    intro kind hkind
    cases kind with
    | tree => rfl
    | back => exact (dfs_tree_edge_not_back G htree hkind).elim
    | forward => exact (dfs_tree_edge_not_forward G htree hkind).elim
    | cross => exact (dfs_tree_edge_not_cross G htree hkind).elim
  · refine ⟨.back, hback, ?_⟩
    intro kind hkind
    cases kind with
    | tree => exact (dfs_tree_edge_not_back G hkind hback).elim
    | back => rfl
    | forward => exact (dfs_forward_edge_not_back G hkind hback).elim
    | cross => exact (dfs_back_edge_not_cross G hback hkind).elim
  · refine ⟨.forward, hforward, ?_⟩
    intro kind hkind
    cases kind with
    | tree => exact (dfs_tree_edge_not_forward G hkind hforward).elim
    | back => exact (dfs_forward_edge_not_back G hforward hkind).elim
    | forward => rfl
    | cross => exact (dfs_forward_edge_not_cross G hforward hkind).elim
  · refine ⟨.cross, hcross, ?_⟩
    intro kind hkind
    cases kind with
    | tree => exact (dfs_tree_edge_not_cross G hkind hcross).elim
    | back => exact (dfs_back_edge_not_cross G hkind hcross).elim
    | forward => exact (dfs_forward_edge_not_cross G hkind hcross).elim
    | cross => rfl

/-- If an edge target is discovered after its source, the target is discovered
during the source's DFS visit and its interval is strictly nested inside the
source's interval. -/
theorem dfs_edge_discovery_lt_implies_intervalNestedInside {u v : V}
    (hadj : G.Adj u v)
    (hdiscovery : discoveryTime (G.dfs) u < discoveryTime (G.dfs) v) :
    intervalNestedInside (G.dfs) u v := by
  have hu : u ∈ G.vertices := G.adj_mem_left hadj
  rcases exists_discovery_state G u hu with
    ⟨s, fuel, huwhite, hu_black, hdisc, hnonwhite, hbf, _hgray,
      hfinish_pres, hfuel, _hlater⟩
  have hvwhite : s.color v = Color.white := by
    by_contra hv
    have hv_early := hnonwhite v hv
    omega
  have hwhite_path : WhiteReachable G s u v :=
    Relation.ReflTransGen.single ⟨hadj, hvwhite⟩
  have hv_black : (dfsVisit G fuel u s).color v = Color.black := by
    apply dfsVisit_white_path_black G huwhite hu hfuel
    exact WhiteReachable.mem_set G hu hwhite_path
  have hfuel_pos : 0 < fuel := by omega
  have hvu : v ≠ u := by
    intro h
    subst v
    omega
  have hfinish_local :
      finishTime (dfsVisit G fuel u s) v < finishTime (dfsVisit G fuel u s) u :=
    dfsVisit_finish_lt_source_finish G hfuel_pos huwhite hbf hvwhite hv_black hvu
  have hfinish : finishTime (G.dfs) v < finishTime (G.dfs) u := by
    rw [hfinish_pres v hv_black, hfinish_pres u hu_black]
    exact hfinish_local
  exact ⟨hdiscovery, hfinish⟩

/-- A graph edge cannot go from a vertex that finishes before its target is
discovered. -/
theorem dfs_edge_not_finishesBeforeDiscovered {u v : V} (hadj : G.Adj u v) :
    ¬finishesBeforeDiscovered (G.dfs) u v := by
  intro hbefore
  have hu : u ∈ G.vertices := G.adj_mem_left hadj
  have hv : v ∈ G.vertices := G.adj_mem_right hadj
  have hduf := G.dfs_discovery_lt_finish hu
  have hdvf := G.dfs_discovery_lt_finish hv
  have hdiscovery : discoveryTime (G.dfs) u < discoveryTime (G.dfs) v := by
    unfold finishesBeforeDiscovered at hbefore
    omega
  have hnested := dfs_edge_discovery_lt_implies_intervalNestedInside G hadj hdiscovery
  unfold finishesBeforeDiscovered at hbefore
  unfold intervalNestedInside at hnested
  omega

/-- For a fixed graph edge, tree or forward classification is equivalent to
the target interval being nested inside the source interval. -/
theorem dfs_tree_or_forward_edge_iff_intervalNestedInside {u v : V}
    (hadj : G.Adj u v) :
    G.IsDFSTreeEdge u v ∨ G.IsDFSForwardEdge u v ↔
      intervalNestedInside (G.dfs) u v := by
  constructor
  · rintro (htree | hforward)
    · have hne : u ≠ v := dfs_parent_ne G htree.2
      exact IsDFSAncestor.intervalNestedInside_dfs G (G.adj_mem_left hadj) hne
        (IsDFSAncestor.single htree.2)
    · exact IsDFSAncestor.intervalNestedInside_dfs G (G.adj_mem_left hadj)
        hforward.2.1 hforward.2.2.1
  · intro hnested
    have hne : u ≠ v := by
      intro h
      subst v
      unfold intervalNestedInside at hnested
      omega
    have hancestor : IsDFSAncestor (G.dfs) u v :=
      intervalNestedInside_dfs_implies_ancestor G
        (G.adj_mem_left hadj) (G.adj_mem_right hadj) hnested
    by_cases hparent : (G.dfs).parent v = some u
    · exact Or.inl ⟨hadj, hparent⟩
    · exact Or.inr ⟨hadj, hne, hancestor, hparent⟩

/-- A forward edge is exactly a nested non-tree graph edge. -/
theorem dfs_forward_edge_iff_intervalNestedInside_and_not_parent {u v : V}
    (hadj : G.Adj u v) :
    G.IsDFSForwardEdge u v ↔
      intervalNestedInside (G.dfs) u v ∧ (G.dfs).parent v ≠ some u := by
  constructor
  · intro hforward
    exact ⟨IsDFSAncestor.intervalNestedInside_dfs G (G.adj_mem_left hadj)
      hforward.2.1 hforward.2.2.1, hforward.2.2.2⟩
  · rintro ⟨hnested, hparent⟩
    have hne : u ≠ v := by
      intro h
      subst v
      unfold intervalNestedInside at hnested
      omega
    exact ⟨hadj, hne,
      intervalNestedInside_dfs_implies_ancestor G
        (G.adj_mem_left hadj) (G.adj_mem_right hadj) hnested,
      hparent⟩

/-- A graph edge is a back edge exactly when it is a self-loop or its source
interval is nested inside its target interval. -/
theorem dfs_back_edge_iff_eq_or_intervalNestedInside {u v : V}
    (hadj : G.Adj u v) :
    G.IsDFSBackEdge u v ↔
      u = v ∨ intervalNestedInside (G.dfs) v u := by
  constructor
  · intro hback
    rcases IsDFSAncestor.eq_or_discovery_lt G hback.2 with hvu | hvu_lt
    · exact Or.inl hvu.symm
    · have hvu : v ≠ u := by
        intro h
        subst v
        omega
      exact Or.inr (IsDFSAncestor.intervalNestedInside_dfs G
        (G.adj_mem_right hadj) hvu hback.2)
  · rintro (huv | hnested)
    · subst v
      exact ⟨hadj, IsDFSAncestor.refl (G.dfs) u⟩
    · exact ⟨hadj, intervalNestedInside_dfs_implies_ancestor G
        (G.adj_mem_right hadj) (G.adj_mem_left hadj) hnested⟩

/-- A graph edge is a cross edge exactly when its target finishes before its
source is discovered. -/
theorem dfs_cross_edge_iff_finishesBeforeDiscovered {u v : V}
    (hadj : G.Adj u v) :
    G.IsDFSCrossEdge u v ↔ finishesBeforeDiscovered (G.dfs) v u := by
  have hu : u ∈ G.vertices := G.adj_mem_left hadj
  have hv : v ∈ G.vertices := G.adj_mem_right hadj
  constructor
  · intro hcross
    have hne : u ≠ v := by
      intro h
      subst v
      exact hcross.2.1 (IsDFSAncestor.refl (G.dfs) u)
    rcases dfs_parenthesis G hu hv hne with h | h | h | h
    · exact (dfs_edge_not_finishesBeforeDiscovered G hadj h).elim
    · exact h
    · exact (hcross.2.1 (intervalNestedInside_dfs_implies_ancestor G hu hv h)).elim
    · exact (hcross.2.2 (intervalNestedInside_dfs_implies_ancestor G hv hu h)).elim
  · intro hbefore
    have hne : u ≠ v := by
      intro h
      subst v
      have hdf := G.dfs_discovery_lt_finish hu
      unfold finishesBeforeDiscovered at hbefore
      omega
    refine ⟨hadj, ?_, ?_⟩
    · intro hancestor
      have hnested := IsDFSAncestor.intervalNestedInside_dfs G hu hne hancestor
      have hvdf := G.dfs_discovery_lt_finish hv
      unfold finishesBeforeDiscovered at hbefore
      unfold intervalNestedInside at hnested
      omega
    · intro hancestor
      have hnested := IsDFSAncestor.intervalNestedInside_dfs G hv hne.symm hancestor
      have hudf := G.dfs_discovery_lt_finish hu
      unfold finishesBeforeDiscovered at hbefore
      unfold intervalNestedInside at hnested
      omega

/-- CLRS timestamp characterization of tree and forward edges. -/
theorem dfs_tree_or_forward_edge_iff_timestamps {u v : V}
    (hadj : G.Adj u v) :
    G.IsDFSTreeEdge u v ∨ G.IsDFSForwardEdge u v ↔
      discoveryTime (G.dfs) u < discoveryTime (G.dfs) v ∧
        finishTime (G.dfs) v < finishTime (G.dfs) u := by
  simpa [intervalNestedInside] using
    (dfs_tree_or_forward_edge_iff_intervalNestedInside G hadj)

/-- CLRS timestamp characterization of back edges, including self-loops. -/
theorem dfs_back_edge_iff_timestamps {u v : V} (hadj : G.Adj u v) :
    G.IsDFSBackEdge u v ↔
      discoveryTime (G.dfs) v ≤ discoveryTime (G.dfs) u ∧
        finishTime (G.dfs) u ≤ finishTime (G.dfs) v := by
  have hu : u ∈ G.vertices := G.adj_mem_left hadj
  have hv : v ∈ G.vertices := G.adj_mem_right hadj
  constructor
  · intro hback
    rcases (dfs_back_edge_iff_eq_or_intervalNestedInside G hadj).1 hback with huv | hnested
    · subst v
      exact ⟨le_rfl, le_rfl⟩
    · unfold intervalNestedInside at hnested
      exact ⟨Nat.le_of_lt hnested.1, Nat.le_of_lt hnested.2⟩
  · intro htimes
    by_cases huv : u = v
    · exact (dfs_back_edge_iff_eq_or_intervalNestedInside G hadj).2 (Or.inl huv)
    rcases dfs_parenthesis G hu hv huv with h | h | h | h
    · have hudf := G.dfs_discovery_lt_finish hu
      unfold finishesBeforeDiscovered at h
      omega
    · have hudf := G.dfs_discovery_lt_finish hu
      unfold finishesBeforeDiscovered at h
      omega
    · unfold intervalNestedInside at h
      omega
    · exact (dfs_back_edge_iff_eq_or_intervalNestedInside G hadj).2 (Or.inr h)

/-- CLRS timestamp characterization of cross edges. -/
theorem dfs_cross_edge_iff_timestamps {u v : V} (hadj : G.Adj u v) :
    G.IsDFSCrossEdge u v ↔
      discoveryTime (G.dfs) v < finishTime (G.dfs) v ∧
        finishTime (G.dfs) v < discoveryTime (G.dfs) u ∧
          discoveryTime (G.dfs) u < finishTime (G.dfs) u := by
  have hu : u ∈ G.vertices := G.adj_mem_left hadj
  have hv : v ∈ G.vertices := G.adj_mem_right hadj
  constructor
  · intro hcross
    have hbefore := (dfs_cross_edge_iff_finishesBeforeDiscovered G hadj).1 hcross
    exact ⟨G.dfs_discovery_lt_finish hv, hbefore, G.dfs_discovery_lt_finish hu⟩
  · rintro ⟨_hvdf, hbefore, _hudf⟩
    exact (dfs_cross_edge_iff_finishesBeforeDiscovered G hadj).2 hbefore

/-- An undirected graph has no cross edges. -/
theorem dfs_undirected_edge_not_cross {u v : V} (hundirected : G.Undirected)
    (hadj : G.Adj u v) : ¬G.IsDFSCrossEdge u v := by
  intro hcross
  have hadj_rev : G.Adj v u := (hundirected u v).mp hadj
  have hcross_rev : G.IsDFSCrossEdge v u :=
    ⟨hadj_rev, hcross.2.2, hcross.2.1⟩
  have huv_times := (dfs_cross_edge_iff_timestamps G hadj).1 hcross
  have hvu_times := (dfs_cross_edge_iff_timestamps G hadj_rev).1 hcross_rev
  omega

/-- **CLRS undirected-edge theorem.** Every edge in an undirected graph is a
tree edge or a back edge when the edge is viewed without orientation. -/
theorem dfs_undirected_edge_tree_or_back {u v : V} (hundirected : G.Undirected)
    (hadj : G.Adj u v) :
    G.IsDFSUndirectedTreeEdge u v ∨ G.IsDFSUndirectedBackEdge u v := by
  rcases dfs_edge_classification G hadj with htree | hback | hforward | hcross
  · exact Or.inl (Or.inl htree)
  · exact Or.inr (Or.inl hback)
  · have hadj_rev : G.Adj v u := (hundirected u v).mp hadj
    exact Or.inr (Or.inr ⟨hadj_rev, hforward.2.2.1⟩)
  · exact (dfs_undirected_edge_not_cross G hundirected hadj hcross).elim

end Graph
end Chapter22
end CLRS
