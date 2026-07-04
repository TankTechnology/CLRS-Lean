import Mathlib

/-! # Section 22.1 - Representing Graphs

This section defines the finite-graph model used by the Chapter 22 algorithm
track.  A graph is a finite vertex set together with an adjacency function.
Undirected graphs are obtained by requiring symmetric adjacency.

The main concepts are:

- {lit}`Graph V`: a directed graph on vertex type `V`.
- {lit}`Graph.Adj u v`: there is a directed edge from `u` to `v`.
- {lit}`Graph.IsWalk p`: `p` is a non-empty list of vertices where each
  consecutive pair is an edge.
- {lit}`Graph.IsPath p`: a walk with no repeated vertices.
- {lit}`Graph.IsCycle p u v`: a non-trivial closed path built from a `u–v`
  path plus the edge {lit}`v → u`.
- {lit}`Graph.Reachable u v`: the reflexive-transitive closure of adjacency.
- {lit}`Graph.ConnectedComponent u`: the set of vertices reachable from `u`.

We define reachability as the reflexive-transitive closure of adjacency; this
makes reflexivity and transitivity immediate and keeps the first pass simple.
The equivalence with the existence of a walk will be proved once the model is
stable.
-/

namespace CLRS
namespace Chapter22

/-- A finite directed graph: a vertex set plus an adjacency function.

We require adjacency to be empty outside the vertex set, so every edge has both
endpoints in {lit}`vertices`. -/
structure Graph (V : Type) [DecidableEq V] where
  vertices : Finset V
  adj : V → Finset V
  adj_sub : ∀ v ∈ vertices, adj v ⊆ vertices
  adj_outside : ∀ v ∉ vertices, adj v = ∅

namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- Directed adjacency: `v` is a neighbor of `u`. -/
def Adj (u v : V) : Prop := v ∈ G.adj u

/-- If `u` is adjacent to `v`, then `u` is a vertex of the graph. -/
theorem adj_mem_left {u v : V} (hadj : G.Adj u v) : u ∈ G.vertices := by
  by_contra h
  have : G.adj u = ∅ := G.adj_outside u h
  simp [Adj, this] at hadj

/-- If `u` is adjacent to `v`, then `v` is a vertex of the graph. -/
theorem adj_mem_right {u v : V} (hadj : G.Adj u v) : v ∈ G.vertices := by
  have hu := G.adj_mem_left hadj
  exact G.adj_sub u hu hadj

/-- A walk is a non-empty vertex list where each consecutive pair is an edge. -/
def IsWalk (p : List V) : Prop :=
  p ≠ [] ∧ (∀ v ∈ p, v ∈ G.vertices) ∧ List.IsChain (fun x y => y ∈ G.adj x) p

/-- `p` is a walk from {lit}`u` to {lit}`v`. -/
def IsWalkFromTo (p : List V) (u v : V) : Prop :=
  G.IsWalk p ∧ p.head? = some u ∧ p.getLast? = some v

/-- A path is a walk with no repeated vertices. -/
def IsPath (p : List V) : Prop :=
  G.IsWalk p ∧ p.Nodup

/-- A cycle is a non-trivial closed path: at least one edge and no repeated
internal vertices.  We represent it as a path from {lit}`u` to {lit}`v` together with an
edge {lit}`v → u`. -/
def IsCycle (p : List V) (u v : V) : Prop :=
  G.IsPath p ∧ p.head? = some u ∧ p.getLast? = some v ∧ v ≠ u ∧ u ∈ G.adj v

/-- Reachability: reflexive-transitive closure of the adjacency relation. -/
def Reachable (u v : V) : Prop :=
  Relation.ReflTransGen G.Adj u v

/-- The connected component of {lit}`u` is the set of vertices reachable from {lit}`u`.

It is a {name}`Set` rather than a {name}`Finset` because the decidable
characterisation of reachability will come from an explicit graph-search
algorithm in later sections. -/
def ConnectedComponent (u : V) : Set V :=
  { v | v ∈ G.vertices ∧ G.Reachable u v }

-- Basic facts about walks.

/-- A single-vertex list is a walk iff the vertex belongs to the graph. -/
theorem isWalk_singleton {u : V} (hu : u ∈ G.vertices) : G.IsWalk [u] := by
  constructor
  · simp
  constructor
  · intro v hv
    simp at hv
    rwa [hv]
  · simp

/-- Adjacency implies a two-vertex walk. -/
theorem isWalk_pair {u v : V} (hu : u ∈ G.vertices) (hadj : G.Adj u v) :
    G.IsWalk [u, v] := by
  have hv : v ∈ G.vertices := G.adj_sub u hu hadj
  constructor
  · simp
  constructor
  · intro a ha
    simp at ha
    cases ha with
    | inl h => rwa [h]
    | inr h => rwa [h]
  · simp [Adj] at hadj ⊢
    exact hadj

-- Reachability is a preorder on vertices.

/-- Reachability is reflexive. -/
theorem reachable_refl (u : V) : G.Reachable u u :=
  Relation.ReflTransGen.refl

/-- Reachability is transitive. -/
theorem reachable_trans {u v w : V}
    (huv : G.Reachable u v) (hvw : G.Reachable v w) : G.Reachable u w :=
  Relation.ReflTransGen.trans huv hvw

/-- An edge implies reachability in one step. -/
theorem reachable_adj {u v : V} (hadj : G.Adj u v) : G.Reachable u v :=
  Relation.ReflTransGen.tail Relation.ReflTransGen.refl hadj

-- Undirected graphs.

/-- An undirected graph has symmetric adjacency. -/
def Undirected (G : Graph V) : Prop :=
  ∀ u v, G.Adj u v ↔ G.Adj v u

/-- In an undirected graph, reachability is symmetric. -/
theorem reachable_symm {G : Graph V} (hund : G.Undirected)
    {u v : V} (huv : G.Reachable u v) : G.Reachable v u := by
  induction huv with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      have hadj' : G.Adj _ _ := (hund _ _).mp hyz
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hadj') ih

end Graph

end Chapter22
end CLRS
