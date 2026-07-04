import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.2 - Breadth-First Search

This section gives an executable breadth-first-search procedure on the finite
graph model from Section 22.1 and proves a soundness theorem: every vertex
reported by BFS is reachable from the source.

The algorithm maintains a set of visited vertices and a FIFO queue.  Each step
pops a vertex `u` from the queue and enqueues every neighbor of `u` that has not
been visited yet.  Because the vertex set is finite, a fuel argument equal to the
number of vertices is enough to ensure termination.

Completeness (every reachable vertex is eventually visited) will be added in a
follow-up pass once the soundness invariant is stable.
-/

namespace CLRS
namespace Chapter22

namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- One step of BFS: pop the front of the queue, mark its unvisited neighbors,
and append them to the queue.  The function is fuelled by a natural number. -/
noncomputable def bfsAux (G : Graph V) (fuel : Nat) (visited : Finset V) (queue : List V) : Finset V :=
  match fuel with
  | 0 => visited
  | fuel + 1 =>
      match queue with
      | [] => visited
      | u :: rest =>
          let newNeighbors := (G.adj u).filter (fun v => v ∉ visited)
          bfsAux G fuel (visited ∪ newNeighbors) (rest ++ newNeighbors.toList)

/-- Breadth-first search from a source vertex `s`.

Returns the set of vertices visited by BFS.  The source must belong to the
graph. -/
noncomputable def bfs (G : Graph V) (s : V) (_hs : s ∈ G.vertices) : Finset V :=
  bfsAux G G.vertices.card ({s} : Finset V) [s]

/-- Soundness invariant for {name}`Graph.bfsAux`: every visited vertex and every
queued vertex is reachable from the source. -/
def BFSInvariant (s : V) (visited : Finset V) (queue : List V) : Prop :=
  (∀ v ∈ visited, G.Reachable s v) ∧ (∀ v ∈ queue, G.Reachable s v)

/-- The BFS step preserves the soundness invariant. -/
theorem bfsInvariant_step {s u : V} {rest : List V} {visited : Finset V}
    (hinv : G.BFSInvariant s visited (u :: rest)) :
    G.BFSInvariant s
      (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
      (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) := by
  rcases hinv with ⟨hvisited, hqueue⟩
  constructor
  · -- visited vertices remain reachable
    intro v hv
    simp [Finset.mem_filter] at hv
    rcases hv with (h | ⟨hadj, _⟩)
    · exact hvisited v h
    · have hu : G.Reachable s u := hqueue u (by simp)
      exact G.reachable_trans hu (G.reachable_adj hadj)
  · -- queued vertices remain reachable
    intro v hv
    simp [List.mem_append, Finset.mem_toList, Finset.mem_filter] at hv
    rcases hv with (h | ⟨hadj, _⟩)
    · exact hqueue v (by simp [h])
    · have hu : G.Reachable s u := hqueue u (by simp)
      exact G.reachable_trans hu (G.reachable_adj hadj)

/-- {name}`Graph.bfsAux` only returns vertices that are reachable from the
source. -/
theorem bfsAux_sound {s : V} (fuel : Nat) (visited : Finset V) (queue : List V)
    (hinv : G.BFSInvariant s visited queue) :
    ∀ v ∈ bfsAux G fuel visited queue, G.Reachable s v := by
  induction fuel generalizing visited queue with
  | zero =>
      intro v hv
      simp [bfsAux] at hv
      exact hinv.1 v hv
  | succ n ih =>
      intro v hv
      cases queue with
      | nil =>
          simp [bfsAux] at hv
          exact hinv.1 v hv
      | cons u rest =>
          simp [bfsAux] at hv
          exact ih (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
                     (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList)
                     (bfsInvariant_step G hinv) v hv

/-- Every vertex reported by {name}`Graph.bfs` is reachable from the source. -/
theorem bfs_sound {s : V} (_hs : s ∈ G.vertices) {v : V}
    (hv : v ∈ bfs G s _hs) : G.Reachable s v := by
  have h : ∀ v ∈ bfs G s _hs, G.Reachable s v := by
    intro v hv
    simp [bfs] at hv
    apply bfsAux_sound G G.vertices.card {s} [s] _ v hv
    constructor
    · intro x hx
      simp at hx
      rw [hx]
      exact G.reachable_refl s
    · intro x hx
      simp at hx
      rw [hx]
      exact G.reachable_refl s
  exact h v hv

end Graph

end Chapter22
end CLRS
