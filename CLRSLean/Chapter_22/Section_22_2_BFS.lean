import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.2 - Breadth-First Search

This section gives an executable breadth-first-search procedure on the finite
graph model from Section 22.1 and proves soundness and completeness theorems:
every vertex reported by BFS is reachable from the source, and every vertex
reachable from the source is reported by BFS.

The algorithm maintains a set of visited vertices and a FIFO queue.  Each step
pops a vertex `u` from the queue and enqueues every neighbor of `u` that has not
been visited yet.  Because the vertex set is finite, a fuel argument equal to the
number of vertices is enough to ensure termination.
-/

namespace CLRS
namespace Chapter22

namespace Graph

variable {V : Type} [DecidableEq V] (G : Graph V)

/-- Internal BFS helper returning both the visited set and the remaining queue.
One step pops the front of the queue, marks its unvisited neighbors, and appends
them to the queue.  The function is fuelled by a natural number. -/
noncomputable def bfsAux' (G : Graph V) (fuel : Nat) (visited : Finset V) (queue : List V) : Finset V × List V :=
  match fuel with
  | 0 => (visited, queue)
  | fuel + 1 =>
      match queue with
      | [] => (visited, [])
      | u :: rest =>
          let newNeighbors := (G.adj u).filter (fun v => v ∉ visited)
          bfsAux' G fuel (visited ∪ newNeighbors) (rest ++ newNeighbors.toList)

/-- One step of BFS returns only the visited set.

`bfsAux` is the public interface: it is the first projection of {name}`bfsAux'`. -/
noncomputable def bfsAux (G : Graph V) (fuel : Nat) (visited : Finset V) (queue : List V) : Finset V :=
  (bfsAux' G fuel visited queue).1

/-- Breadth-first search from a source vertex `s`.

Returns the set of vertices visited by BFS.  The source must belong to the
graph. -/
noncomputable def bfs (G : Graph V) (s : V) (_hs : s ∈ G.vertices) : Finset V :=
  bfsAux G G.vertices.card ({s} : Finset V) [s]

/-- Soundness invariant for {name}`Graph.bfsAux'`: every visited vertex and every
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

/-- {name}`Graph.bfsAux'` only returns vertices that are reachable from the
source. -/
theorem bfsAux'_sound {s : V} (fuel : Nat) (visited : Finset V) (queue : List V)
    (hinv : G.BFSInvariant s visited queue) :
    ∀ v ∈ (bfsAux' G fuel visited queue).1, G.Reachable s v := by
  induction fuel generalizing visited queue with
  | zero =>
      intro v hv
      simp [bfsAux'] at hv
      exact hinv.1 v hv
  | succ n ih =>
      intro v hv
      cases queue with
      | nil =>
          simp [bfsAux'] at hv
          exact hinv.1 v hv
      | cons u rest =>
          simp [bfsAux'] at hv
          exact ih (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
                     (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList)
                     (bfsInvariant_step G hinv) v hv

/-- {name}`Graph.bfsAux` only returns vertices that are reachable from the
source. -/
theorem bfsAux_sound {s : V} (fuel : Nat) (visited : Finset V) (queue : List V)
    (hinv : G.BFSInvariant s visited queue) :
    ∀ v ∈ bfsAux G fuel visited queue, G.Reachable s v := by
  intro v hv
  simp [bfsAux] at hv ⊢
  exact bfsAux'_sound G fuel visited queue hinv v hv

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

-- =============================================================================
--  Completeness: every reachable vertex is visited
-- =============================================================================

/-- The visited set returned by {name}`Graph.bfsAux'` is monotone in the input
visited set: every vertex already visited stays visited. -/
theorem bfsAux'_visited_monotone {fuel : Nat} {visited : Finset V} {queue : List V} {v : V}
    (hv : v ∈ visited) : v ∈ (bfsAux' G fuel visited queue).1 := by
  induction fuel generalizing visited queue with
  | zero =>
      simp [bfsAux']
      exact hv
  | succ n ih =>
      cases queue with
      | nil =>
          simp [bfsAux']
          exact hv
      | cons u rest =>
          simp [bfsAux']
          apply ih
          simp [hv]

/-- Closure invariant for BFS: every processed vertex (visited but no longer in
the queue) has all of its neighbors already visited. -/
def BFSClosedInv (G : Graph V) (visited : Finset V) (queue : List V) : Prop :=
  ∀ u ∈ visited, u ∉ queue → ∀ v ∈ G.adj u, v ∈ visited

/-- Queue invariant for BFS: every queued vertex is already marked visited. -/
def BFSQueueInv (G : Graph V) (visited : Finset V) (queue : List V) : Prop :=
  ∀ v ∈ queue, v ∈ visited

/-- The closure invariant is preserved by one BFS step. -/
theorem bfsClosedInv_step {u : V} {rest : List V} {visited : Finset V}
    (hclosed : BFSClosedInv G visited (u :: rest)) :
    BFSClosedInv G
      (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
      (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) := by
  intro x hx hxnotin v hvx
  simp [BFSClosedInv] at hclosed
  simp [Finset.mem_union, Finset.mem_filter] at hx
  rcases hx with (hx | ⟨hxadj, hxnvis⟩)
  · -- x was already visited before this step
    by_cases hxu : x = u
    · -- x = u, so all its neighbors (including v) are now visited
      rw [hxu] at hvx
      simp [hvx]
      by_cases h : v ∈ visited <;> simp [h]
    · -- x ≠ u
      by_cases hxrest : x ∈ rest
      · -- x is still in the new queue, no obligation
        exfalso
        simp [hxrest] at hxnotin
      · -- x has been processed before; its neighbors were already visited
        have hxnotin' : x ∉ u :: rest := by
          simp [hxu, hxrest]
        have hxne : x ≠ u := by
          intro h
          apply hxnotin'
          simp [h]
        have hxnrest : x ∉ rest := by
          intro h
          apply hxnotin'
          simp [h]
        have : v ∈ visited := hclosed x hx hxne hxnrest v hvx
        simp [this]
  · -- x is newly discovered, so it is enqueued and we have no obligation
    exfalso
    have : x ∈ rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList := by
      simp [hxadj, hxnvis]
    contradiction

/-- The queue invariant is preserved by one BFS step. -/
theorem bfsQueueInv_step {u : V} {rest : List V} {visited : Finset V}
    (hqueue : G.BFSQueueInv visited (u :: rest)) :
    G.BFSQueueInv
      (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
      (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) := by
  intro x hx
  simp [BFSQueueInv] at hqueue
  rcases hqueue with ⟨hu, hrest⟩
  simp [List.mem_append, Finset.mem_toList, Finset.mem_filter] at hx
  rcases hx with (hx | ⟨hxadj, hxnvis⟩)
  · -- x was already in the rest of the queue
    have : x ∈ visited := hrest x hx
    simp [this]
  · -- x is a newly enqueued neighbor of u
    simp [hxadj, hxnvis]

/-- Termination measure for BFS: length of the queue plus the number of
unvisited vertices.  It decreases by exactly one on every productive step. -/
def bfsMeasure (G : Graph V) (visited : Finset V) (queue : List V) : Nat :=
  queue.length + (G.vertices \ visited).card

/-- A productive BFS step strictly decreases the measure by one. -/
theorem bfsMeasure_decreasing {u : V} {rest : List V} {visited : Finset V} :
    bfsMeasure G (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
                   (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList)
    = bfsMeasure G visited (u :: rest) - 1 := by
  set newNeighbors := (G.adj u).filter (fun v => v ∉ visited)
  simp [bfsMeasure]
  have hsub : newNeighbors ⊆ G.vertices \ visited := by
    intro x hx
    simp [newNeighbors, Finset.mem_filter, Finset.mem_sdiff] at hx ⊢
    constructor
    · exact G.adj_sub u (G.adj_mem_left (show G.Adj u x by simp [Adj] at hx ⊢; exact hx.1)) hx.1
    · exact hx.2
  have heq : G.vertices \ (visited ∪ newNeighbors) = (G.vertices \ visited) \ newNeighbors := by
    ext x
    simp
    tauto
  have hcard : ((G.vertices \ visited) \ newNeighbors).card =
               (G.vertices \ visited).card - newNeighbors.card := by
    have h1 : ((G.vertices \ visited) \ newNeighbors).card =
              (G.vertices \ visited).card - (newNeighbors ∩ (G.vertices \ visited)).card := by
      rw [Finset.card_sdiff]
    have h2 : newNeighbors ∩ (G.vertices \ visited) = newNeighbors := by
      ext x
      simp [Finset.mem_sdiff]
      intro h
      have := hsub h
      simp [Finset.mem_sdiff] at this
      exact this
    rw [h1, h2]
  have hle : newNeighbors.card ≤ (G.vertices \ visited).card := Finset.card_le_card hsub
  rw [heq, hcard]
  omega

/-- With enough fuel, {name}`Graph.bfsAux'` empties the queue. -/
theorem bfsAux'_queue_empty {fuel : Nat} {visited : Finset V} {queue : List V}
    (hmeas : bfsMeasure G visited queue ≤ fuel) :
    (bfsAux' G fuel visited queue).2 = [] := by
  induction fuel generalizing visited queue with
  | zero =>
      simp [bfsMeasure] at hmeas
      cases queue with
      | nil => simp [bfsAux']
      | cons u rest => simp at hmeas
  | succ n ih =>
      cases queue with
      | nil =>
          simp [bfsAux']
      | cons u rest =>
          simp [bfsAux']
          have hmeas' : bfsMeasure G (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
                                  (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) ≤ n := by
            rw [bfsMeasure_decreasing G]
            omega
          exact ih hmeas'

/-- With enough fuel, {name}`Graph.bfsAux'` preserves the closure invariant. -/
theorem bfsAux'_closed {fuel : Nat} {visited : Finset V} {queue : List V}
    (hclosed : G.BFSClosedInv visited queue) (hmeas : bfsMeasure G visited queue ≤ fuel) :
    G.BFSClosedInv (bfsAux' G fuel visited queue).1 (bfsAux' G fuel visited queue).2 := by
  induction fuel generalizing visited queue with
  | zero =>
      simp [bfsAux']
      exact hclosed
  | succ n ih =>
      cases queue with
      | nil =>
          simp [bfsAux']
          exact hclosed
      | cons u rest =>
          simp [bfsAux']
          have hclosed' : G.BFSClosedInv
              (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
              (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) :=
            bfsClosedInv_step G hclosed
          have hmeas' : bfsMeasure G (visited ∪ (G.adj u).filter (fun v => v ∉ visited))
                                  (rest ++ ((G.adj u).filter (fun v => v ∉ visited)).toList) ≤ n := by
            rw [bfsMeasure_decreasing G]
            omega
          exact ih hclosed' hmeas'

/-- Every vertex visited by {name}`Graph.bfs` has all of its neighbors visited.
This is the key lemma for completeness. -/
theorem bfs_closed {s : V} (_hs : s ∈ G.vertices) :
    ∀ u ∈ bfs G s _hs, ∀ v ∈ G.adj u, v ∈ bfs G s _hs := by
  simp [bfs, bfsAux]
  have hclosed : G.BFSClosedInv ({s} : Finset V) [s] := by
    intro u hu huin v hv
    simp at hu huin
    rw [hu] at huin
    contradiction
  have hmeas : bfsMeasure G ({s} : Finset V) [s] ≤ G.vertices.card := by
    simp [bfsMeasure]
    have hcard : (G.vertices \ ({s} : Finset V)).card = G.vertices.card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase]
      apply Finset.card_erase_of_mem
      exact _hs
    rw [hcard]
    have hpos : G.vertices.card ≥ 1 := by
      apply Finset.one_le_card.mpr
      use s
    omega
  have hclosed' := bfsAux'_closed G hclosed hmeas
  have hempty := bfsAux'_queue_empty G hmeas
  rw [hempty] at hclosed'
  intro u hu v hv
  exact hclosed' u hu (by simp) v hv

/-- Every vertex reachable from the source is reported by {name}`Graph.bfs`. -/
theorem bfs_complete {s : V} (_hs : s ∈ G.vertices) {v : V} (hreach : G.Reachable s v) :
    v ∈ bfs G s _hs := by
  -- Helper: once a vertex is in the BFS visited set, all vertices reachable from
  -- it remain in that same visited set.
  have hclosure {src u w : V} (_hsrc : src ∈ G.vertices) (hu : u ∈ bfs G src _hsrc)
      (hw : G.Reachable u w) : w ∈ bfs G src _hsrc := by
    induction hw with
    | refl => exact hu
    | tail _ hadj ih => exact bfs_closed G _hsrc _ ih _ hadj
  -- Main proof by head induction on the reachability witness.
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      apply bfsAux'_visited_monotone G
      simp
  | @head a c h' h ih =>
      have _hc : c ∈ G.vertices := G.adj_sub a (G.adj_mem_left h') h'
      have hcv : v ∈ bfs G c _hc := ih _hc
      have _ha : a ∈ G.vertices := G.adj_mem_left h'
      have ha_bfs : a ∈ bfs G a _ha := by
        apply bfsAux'_visited_monotone G
        simp
      have hc_in_a : c ∈ bfs G a _ha := bfs_closed G _ha a ha_bfs c h'
      have hreach_c_v : G.Reachable c v := G.bfs_sound _hc hcv
      exact hclosure _ha hc_in_a hreach_c_v

end Graph

end Chapter22
end CLRS
