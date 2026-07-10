import Mathlib
import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs

/-! # Section 22.2 - Breadth-First Search

This section gives executable breadth-first-search procedures on the finite
graph model from Section 22.1.  The basic search is proved sound and complete
for reachability.  A CLRS-labelled version additionally records distances and
predecessors; its distances are proved to be unweighted shortest-path lengths,
and its parent pointers are proved to form a rooted predecessor tree spanning
exactly the reachable vertices.

The algorithm maintains a set of visited vertices and a FIFO queue.  Each step
pops a vertex {lit}`u` from the queue and enqueues every neighbor of {lit}`u`
that has not been visited yet.  Because the vertex set is finite, a fuel
argument equal to the number of vertices is enough to ensure termination.

The main correctness theorems are {lit}`bfsState_distance_eq_some_iff`,
{lit}`bfsState_isBFSPredecessorTree`, and the combined
{lit}`bfsState_correct`.
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

{lit}`bfsAux` is the public interface: it is the first projection of {name}`bfsAux'`. -/
noncomputable def bfsAux (G : Graph V) (fuel : Nat) (visited : Finset V) (queue : List V) : Finset V :=
  (bfsAux' G fuel visited queue).1

/-- Breadth-first search from a source vertex {lit}`s`.

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
def BFSQueueInv (_G : Graph V) (visited : Finset V) (queue : List V) : Prop :=
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

-- =============================================================================
--  CLRS distance and predecessor state
-- =============================================================================

/-- Reachability by exactly {lit}`n` directed edges. -/
inductive ReachableIn (G : Graph V) (s : V) : V → Nat → Prop where
  | refl : G.ReachableIn s s 0
  | tail {u v : V} {n : Nat} :
      G.ReachableIn s u n → G.Adj u v → G.ReachableIn s v (n + 1)

/-- A natural number is the unweighted shortest-path distance from {lit}`s` to
{lit}`v` when it is attained by a walk and lower-bounds every other such walk. -/
def IsShortestDistance (G : Graph V) (s v : V) (distance : Nat) : Prop :=
  G.ReachableIn s v distance ∧
    ∀ length, G.ReachableIn s v length → distance ≤ length

/-- Exact-length reachability implies ordinary reachability. -/
theorem ReachableIn.reachable {s v : V} {n : Nat}
    (h : G.ReachableIn s v n) : G.Reachable s v := by
  induction h with
  | refl => exact G.reachable_refl s
  | tail hreach hadj ih => exact G.reachable_trans ih (G.reachable_adj hadj)

/-- A shortest-distance witness always gives ordinary reachability. -/
theorem IsShortestDistance.reachable {s v : V} {n : Nat}
    (h : G.IsShortestDistance s v n) : G.Reachable s v :=
  h.1.reachable G

/-- Mutable CLRS BFS state.  A vertex is discovered exactly when it belongs to
{lit}`visited`; {lit}`distance` and {lit}`parent` record its first discovery. -/
structure BFSState (V : Type) [DecidableEq V] where
  visited : Finset V
  queue : List V
  distance : V → Option Nat
  parent : V → Option V

namespace BFSState

/-- Numeric level used by the queue invariants.  It is only inspected for
discovered vertices, where the distance is known to be present. -/
def level (state : BFSState V) (v : V) : Nat :=
  (state.distance v).getD 0

end BFSState

/-- Initial labelled BFS state. -/
noncomputable def bfsStateInit (s : V) : BFSState V where
  visited := {s}
  queue := [s]
  distance := fun v => if v = s then some 0 else none
  parent := fun _ => none

/-- As-yet undiscovered out-neighbors of {lit}`u`. -/
noncomputable def bfsNewNeighbors (G : Graph V) (state : BFSState V) (u : V) : Finset V :=
  (G.adj u).filter (fun v => v ∉ state.visited)

/-- Process the front vertex {lit}`u`, assigning distance {lit}`d[u] + 1` and
parent {lit}`u` to every newly discovered neighbor. -/
noncomputable def bfsStateAdvance (G : Graph V) (state : BFSState V)
    (u : V) (rest : List V) : BFSState V :=
  let newNeighbors := bfsNewNeighbors G state u
  let nextDistance := state.level u + 1
  {
    visited := state.visited ∪ newNeighbors
    queue := rest ++ newNeighbors.toList
    distance := fun v =>
      if v ∈ newNeighbors then some nextDistance else state.distance v
    parent := fun v =>
      if v ∈ newNeighbors then some u else state.parent v
  }

/-- Fuelled labelled BFS. -/
noncomputable def bfsStateAux (G : Graph V) : Nat → BFSState V → BFSState V
  | 0, state => state
  | fuel + 1, state =>
      match state.queue with
      | [] => state
      | u :: rest => bfsStateAux G fuel (bfsStateAdvance G state u rest)

/-- CLRS BFS result with distances and predecessor pointers. -/
noncomputable def bfsState (G : Graph V) (s : V) (_hs : s ∈ G.vertices) : BFSState V :=
  bfsStateAux G G.vertices.card (bfsStateInit s)

/-- The labelled BFS has exactly the same visited-set and queue evolution as
the already verified reachability-only BFS. -/
theorem bfsStateAux_search_eq (fuel : Nat) (state : BFSState V) :
    let result := bfsStateAux G fuel state
    (result.visited, result.queue) =
      bfsAux' G fuel state.visited state.queue := by
  induction fuel generalizing state with
  | zero => simp [bfsStateAux, bfsAux']
  | succ fuel ih =>
      cases hqueue : state.queue with
      | nil => simp [bfsStateAux, bfsAux', hqueue]
      | cons u rest =>
          simp only [bfsStateAux, bfsAux', hqueue]
          simpa [bfsStateAdvance, bfsNewNeighbors] using
            ih (bfsStateAdvance G state u rest)

/-- The final labelled BFS discovers exactly the vertices returned by
{name}`Graph.bfs`. -/
theorem bfsState_visited_eq_bfs {s : V} (hs : s ∈ G.vertices) :
    (bfsState G s hs).visited = bfs G s hs := by
  have h := bfsStateAux_search_eq G G.vertices.card (bfsStateInit s)
  have hfirst := congrArg Prod.fst h
  simpa [bfsState, bfs, bfsAux, bfsStateInit] using hfirst

/-- The final labelled BFS has exhausted its queue. -/
theorem bfsState_queue_empty {s : V} (hs : s ∈ G.vertices) :
    (bfsState G s hs).queue = [] := by
  have h := bfsStateAux_search_eq G G.vertices.card (bfsStateInit s)
  have hsecond := congrArg Prod.snd h
  have hmeasure : bfsMeasure G ({s} : Finset V) [s] ≤ G.vertices.card := by
    simp [bfsMeasure]
    have hcard : (G.vertices \ ({s} : Finset V)).card = G.vertices.card - 1 := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact Finset.card_erase_of_mem hs
    rw [hcard]
    have hpositive : 1 ≤ G.vertices.card := Finset.one_le_card.mpr ⟨s, hs⟩
    omega
  have hempty := bfsAux'_queue_empty G hmeasure
  simpa [bfsState, bfsStateInit] using hsecond.trans hempty

/-- Invariant connecting the FIFO search state to CLRS distance and predecessor
labels.  The queue is ordered by nondecreasing level and spans at most two
consecutive levels; processed edges already satisfy the shortest-path upper
bound needed at termination. -/
structure BFSDistanceInvariant (G : Graph V) (s : V) (state : BFSState V) : Prop where
  closed : G.BFSClosedInv state.visited state.queue
  queued : G.BFSQueueInv state.visited state.queue
  source_distance : state.distance s = some 0
  source_parent : state.parent s = none
  distance_iff_visited : ∀ v, v ∈ state.visited ↔ ∃ d, state.distance v = some d
  distance_zero : ∀ v, state.distance v = some 0 → v = s
  parent_exists : ∀ v, v ∈ state.visited → v ≠ s → ∃ u, state.parent v = some u
  parent_unvisited : ∀ v, v ∉ state.visited → state.parent v = none
  parent_step : ∀ u v, state.parent v = some u →
    G.Adj u v ∧ ∃ d, state.distance u = some d ∧ state.distance v = some (d + 1)
  queue_ordered : state.queue.Pairwise (fun u v => state.level u ≤ state.level v)
  visited_span : ∀ u rest, state.queue = u :: rest →
    ∀ v ∈ state.visited, state.level v ≤ state.level u + 1
  processed_edge : ∀ u ∈ state.visited, u ∉ state.queue →
    ∀ v, G.Adj u v → state.level v ≤ state.level u + 1

@[simp]
theorem mem_bfsNewNeighbors_iff {state : BFSState V} {u v : V} :
    v ∈ bfsNewNeighbors G state u ↔ G.Adj u v ∧ v ∉ state.visited := by
  simp [bfsNewNeighbors, Adj]

/-- Processing a vertex does not change labels of already discovered vertices. -/
theorem bfsStateAdvance_distance_of_visited {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance G state u rest).distance v = state.distance v := by
  have hvnew : v ∉ bfsNewNeighbors G state u := by
    simp [mem_bfsNewNeighbors_iff, hv]
  simp [bfsStateAdvance, hvnew]

theorem bfsStateAdvance_parent_of_visited {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance G state u rest).parent v = state.parent v := by
  have hvnew : v ∉ bfsNewNeighbors G state u := by
    simp [mem_bfsNewNeighbors_iff, hv]
  simp [bfsStateAdvance, hvnew]

theorem bfsStateAdvance_level_of_visited {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance G state u rest).level v = state.level v := by
  simp [BFSState.level, bfsStateAdvance_distance_of_visited G hv]

/-- Every newly discovered vertex receives the front vertex's level plus one
and records the front vertex as its parent. -/
theorem bfsStateAdvance_distance_of_new {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors G state u) :
    (bfsStateAdvance G state u rest).distance v = some (state.level u + 1) := by
  simp [bfsStateAdvance, hv]

theorem bfsStateAdvance_parent_of_new {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors G state u) :
    (bfsStateAdvance G state u rest).parent v = some u := by
  simp [bfsStateAdvance, hv]

theorem bfsStateAdvance_level_of_new {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors G state u) :
    (bfsStateAdvance G state u rest).level v = state.level u + 1 := by
  simp [BFSState.level, bfsStateAdvance_distance_of_new G hv]

/-- The initial labelled state satisfies all distance and predecessor
invariants. -/
theorem bfsDistanceInvariant_init {s : V} :
    G.BFSDistanceInvariant s (bfsStateInit s) := by
  constructor <;> simp [BFSClosedInv, BFSQueueInv, bfsStateInit, BFSState.level]

/-- One FIFO step preserves the distance and predecessor invariant. -/
theorem bfsDistanceInvariant_step {s u : V} {rest : List V} {state : BFSState V}
    (hqueue : state.queue = u :: rest)
    (hinv : G.BFSDistanceInvariant s state) :
    G.BFSDistanceInvariant s (bfsStateAdvance G state u rest) := by
  have hu_queue : u ∈ state.queue := by simp [hqueue]
  have hu_visited : u ∈ state.visited := hinv.queued u hu_queue
  have hu_not_new : u ∉ bfsNewNeighbors G state u := by
    simp [mem_bfsNewNeighbors_iff, hu_visited]
  have hclosed : G.BFSClosedInv state.visited (u :: rest) := by
    simpa [hqueue] using hinv.closed
  have hqueued : G.BFSQueueInv state.visited (u :: rest) := by
    simpa [hqueue] using hinv.queued
  have hs_visited : s ∈ state.visited :=
    (hinv.distance_iff_visited s).2 ⟨0, hinv.source_distance⟩
  have hs_not_new : s ∉ bfsNewNeighbors G state u := by
    simp [mem_bfsNewNeighbors_iff, hs_visited]
  have hordered : (u :: rest).Pairwise
      (fun a b => state.level a ≤ state.level b) := by
    simpa [hqueue] using hinv.queue_ordered
  constructor
  · simpa [bfsStateAdvance, bfsNewNeighbors] using
      (bfsClosedInv_step G hclosed)
  · simpa [bfsStateAdvance, bfsNewNeighbors] using
      (bfsQueueInv_step G hqueued)
  · simpa [bfsStateAdvance, hs_not_new] using hinv.source_distance
  · simpa [bfsStateAdvance, hs_not_new] using hinv.source_parent
  · intro v
    constructor
    · intro hv
      change v ∈ state.visited ∪ bfsNewNeighbors G state u at hv
      rcases Finset.mem_union.mp hv with hvold | hvnew
      · rcases (hinv.distance_iff_visited v).1 hvold with ⟨d, hd⟩
        exact ⟨d, by simpa [bfsStateAdvance_distance_of_visited G hvold] using hd⟩
      · exact ⟨state.level u + 1, bfsStateAdvance_distance_of_new G hvnew⟩
    · rintro ⟨d, hd⟩
      by_cases hvnew : v ∈ bfsNewNeighbors G state u
      · exact Finset.mem_union_right _ hvnew
      · have hdold : state.distance v = some d := by
          simpa [bfsStateAdvance, hvnew] using hd
        exact Finset.mem_union_left _ ((hinv.distance_iff_visited v).2 ⟨d, hdold⟩)
  · intro v hvzero
    by_cases hvnew : v ∈ bfsNewNeighbors G state u
    · have := bfsStateAdvance_distance_of_new G (rest := rest) hvnew
      rw [hvzero] at this
      simp at this
    · have hvold : state.distance v = some 0 := by
        simpa [bfsStateAdvance, hvnew] using hvzero
      exact hinv.distance_zero v hvold
  · intro v hv hvs
    change v ∈ state.visited ∪ bfsNewNeighbors G state u at hv
    rcases Finset.mem_union.mp hv with hvold | hvnew
    · rcases hinv.parent_exists v hvold hvs with ⟨p, hp⟩
      exact ⟨p, by simpa [bfsStateAdvance_parent_of_visited G hvold] using hp⟩
    · exact ⟨u, bfsStateAdvance_parent_of_new G hvnew⟩
  · intro v hv
    have hvold : v ∉ state.visited := by
      intro h
      exact hv (Finset.mem_union_left _ h)
    have hvnew : v ∉ bfsNewNeighbors G state u := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    simpa [bfsStateAdvance, hvnew] using hinv.parent_unvisited v hvold
  · intro p v hp
    by_cases hvnew : v ∈ bfsNewNeighbors G state u
    · have hp_eq : p = u := by
        have hnewParent := bfsStateAdvance_parent_of_new G (rest := rest) hvnew
        rw [hp] at hnewParent
        exact Option.some.inj hnewParent
      subst p
      have hadj : G.Adj u v := (mem_bfsNewNeighbors_iff G).1 hvnew |>.1
      rcases (hinv.distance_iff_visited u).1 hu_visited with ⟨d, hd⟩
      have hlevel : state.level u = d := by simp [BFSState.level, hd]
      refine ⟨hadj, d, ?_, ?_⟩
      simpa [bfsStateAdvance_distance_of_visited G hu_visited] using hd
      simpa [hlevel] using bfsStateAdvance_distance_of_new G (rest := rest) hvnew
    · have hpold : state.parent v = some p := by
        simpa [bfsStateAdvance, hvnew] using hp
      rcases hinv.parent_step p v hpold with ⟨hadj, d, hdp, hdv⟩
      have hp_visited : p ∈ state.visited :=
        (hinv.distance_iff_visited p).2 ⟨d, hdp⟩
      have hv_visited : v ∈ state.visited :=
        (hinv.distance_iff_visited v).2 ⟨d + 1, hdv⟩
      refine ⟨hadj, d, ?_, ?_⟩
      · simpa [bfsStateAdvance_distance_of_visited G hp_visited] using hdp
      · simpa [bfsStateAdvance_distance_of_visited G hv_visited] using hdv
  · change (rest ++ (bfsNewNeighbors G state u).toList).Pairwise
      (fun a b => (bfsStateAdvance G state u rest).level a ≤
        (bfsStateAdvance G state u rest).level b)
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · have hrest := hordered.tail
      rw [List.pairwise_iff_get] at hrest ⊢
      intro i j hij
      have hi_visited : rest.get i ∈ state.visited := hqueued _ (by simp)
      have hj_visited : rest.get j ∈ state.visited := hqueued _ (by simp)
      rw [bfsStateAdvance_level_of_visited G (rest := rest) hi_visited,
        bfsStateAdvance_level_of_visited G (rest := rest) hj_visited]
      exact hrest i j hij
    · apply List.pairwise_of_reflexive_of_forall_ne
      intro a ha b hb _
      have ha_new : a ∈ bfsNewNeighbors G state u := Finset.mem_toList.mp ha
      have hb_new : b ∈ bfsNewNeighbors G state u := Finset.mem_toList.mp hb
      rw [bfsStateAdvance_level_of_new G ha_new,
        bfsStateAdvance_level_of_new G hb_new]
    · intro a ha b hb
      have ha_visited : a ∈ state.visited := hqueued a (by simp [ha])
      have hb_new : b ∈ bfsNewNeighbors G state u := Finset.mem_toList.mp hb
      rw [bfsStateAdvance_level_of_visited G ha_visited,
        bfsStateAdvance_level_of_new G hb_new]
      exact hinv.visited_span u rest hqueue a ha_visited
  · intro front tail hnext_queue v hv
    have hv_union : v ∈ state.visited ∪ bfsNewNeighbors G state u := by
      simpa [bfsStateAdvance] using hv
    have hv_bound : (bfsStateAdvance G state u rest).level v ≤ state.level u + 1 := by
      rcases Finset.mem_union.mp hv_union with hvold | hvnew
      · rw [bfsStateAdvance_level_of_visited G hvold]
        exact hinv.visited_span u rest hqueue v hvold
      · rw [bfsStateAdvance_level_of_new G hvnew]
    cases rest with
    | nil =>
        have hlist : (bfsNewNeighbors G state u).toList = front :: tail := by
          simpa [bfsStateAdvance] using hnext_queue
        have hfront_new : front ∈ bfsNewNeighbors G state u := by
          apply Finset.mem_toList.mp
          rw [hlist]
          simp
        rw [bfsStateAdvance_level_of_new G hfront_new]
        omega
    | cons next remaining =>
        have hlist : next :: (remaining ++ (bfsNewNeighbors G state u).toList) =
            front :: tail := by
          simpa [bfsStateAdvance] using hnext_queue
        have hfront : front = next := by
          injection hlist with hhead _
          exact hhead.symm
        subst front
        have hnext_visited : next ∈ state.visited := hqueued next (by simp)
        have hu_le_next : state.level u ≤ state.level next :=
          List.rel_of_pairwise_cons hordered (by simp)
        rw [bfsStateAdvance_level_of_visited G hnext_visited]
        omega
  · intro x hx hnotin y hxy
    have hx_union : x ∈ state.visited ∪ bfsNewNeighbors G state u := by
      simpa [bfsStateAdvance] using hx
    rcases Finset.mem_union.mp hx_union with hxold | hxnew
    · by_cases hxu : x = u
      · subst x
        by_cases hyold : y ∈ state.visited
        · rw [bfsStateAdvance_level_of_visited G hyold,
            bfsStateAdvance_level_of_visited G hu_visited]
          exact hinv.visited_span u rest hqueue y hyold
        · have hynew : y ∈ bfsNewNeighbors G state u :=
            (mem_bfsNewNeighbors_iff G).2 ⟨hxy, hyold⟩
          rw [bfsStateAdvance_level_of_new G hynew,
            bfsStateAdvance_level_of_visited G hu_visited]
      · have hx_not_rest : x ∉ rest := by
          intro hxrest
          apply hnotin
          change x ∈ rest ++ (bfsNewNeighbors G state u).toList
          exact List.mem_append_left _ hxrest
        have hx_not_queue : x ∉ state.queue := by
          rw [hqueue]
          simp [hxu, hx_not_rest]
        have hyold : y ∈ state.visited := hclosed x hxold (by
          simp [hxu, hx_not_rest]) y hxy
        rw [bfsStateAdvance_level_of_visited G hyold,
          bfsStateAdvance_level_of_visited G hxold]
        exact hinv.processed_edge x hxold hx_not_queue y hxy
    · exfalso
      apply hnotin
      change x ∈ rest ++ (bfsNewNeighbors G state u).toList
      exact List.mem_append_right _ (Finset.mem_toList.mpr hxnew)

/-- Every fuelled execution preserves the distance invariant. -/
theorem bfsDistanceInvariant_aux {s : V} (fuel : Nat) (state : BFSState V)
    (hinv : G.BFSDistanceInvariant s state) :
    G.BFSDistanceInvariant s (bfsStateAux G fuel state) := by
  induction fuel generalizing state with
  | zero => simpa [bfsStateAux]
  | succ fuel ih =>
      cases hqueue : state.queue with
      | nil => simpa [bfsStateAux, hqueue]
      | cons u rest =>
          simp only [bfsStateAux, hqueue]
          exact ih (bfsStateAdvance G state u rest)
            (bfsDistanceInvariant_step G hqueue hinv)

/-- The final CLRS BFS state satisfies the distance invariant. -/
theorem bfsState_distanceInvariant {s : V} (hs : s ∈ G.vertices) :
    G.BFSDistanceInvariant s (bfsState G s hs) := by
  simpa [bfsState] using
    (bfsDistanceInvariant_aux G G.vertices.card (bfsStateInit s)
      (bfsDistanceInvariant_init G))

/-- Ordinary reachability is equivalent to exact reachability for some finite
number of edges. -/
theorem reachable_iff_exists_reachableIn {s v : V} :
    G.Reachable s v ↔ ∃ n, G.ReachableIn s v n := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, ReachableIn.refl⟩
    | tail _ hadj ih =>
        rcases ih with ⟨n, hn⟩
        exact ⟨n + 1, ReachableIn.tail hn hadj⟩
  · rintro ⟨n, h⟩
    exact h.reachable G

/-- A path following the recorded parent function from the source. -/
inductive BFSParentPath (parent : V → Option V) (s : V) : V → Nat → Prop where
  | root : BFSParentPath parent s s 0
  | tail {u v : V} {n : Nat} :
      BFSParentPath parent s u n → parent v = some u →
        BFSParentPath parent s v (n + 1)

/-- Every distance label maintained by the invariant is witnessed by a parent
path of exactly that length. -/
theorem BFSDistanceInvariant.parentPath_of_distance
    {s : V} {state : BFSState V} (hinv : G.BFSDistanceInvariant s state)
    {v : V} {distance : Nat} (hdistance : state.distance v = some distance) :
    BFSParentPath state.parent s v distance := by
  induction distance using Nat.strong_induction_on generalizing v with
  | h distance ih =>
      cases distance with
      | zero =>
          have hvs : v = s := hinv.distance_zero v hdistance
          subst v
          exact BFSParentPath.root
      | succ n =>
          have hv_visited : v ∈ state.visited :=
            (hinv.distance_iff_visited v).2 ⟨n + 1, hdistance⟩
          have hvs : v ≠ s := by
            intro h
            subst v
            rw [hinv.source_distance] at hdistance
            simp at hdistance
          rcases hinv.parent_exists v hv_visited hvs with ⟨u, hparent⟩
          rcases hinv.parent_step u v hparent with ⟨_, d, hdu, hdv⟩
          have hdn : d = n := by
            rw [hdistance] at hdv
            simp at hdv
            omega
          subst d
          exact BFSParentPath.tail (ih n (by omega) hdu) hparent

/-- Parent paths in a valid BFS state are graph paths with the same number of
edges. -/
theorem BFSDistanceInvariant.parentPath_reachableIn
    {s : V} {state : BFSState V} (hinv : G.BFSDistanceInvariant s state)
    {v : V} {distance : Nat} (hpath : BFSParentPath state.parent s v distance) :
    G.ReachableIn s v distance := by
  induction hpath with
  | root => exact ReachableIn.refl
  | tail hpath hparent ih =>
      exact ReachableIn.tail ih (hinv.parent_step _ _ hparent).1

/-- Every recorded distance is attained by a graph path of exactly that
length. -/
theorem bfsState_distance_reachableIn {s v : V} (hs : s ∈ G.vertices)
    {distance : Nat} (hdistance : (bfsState G s hs).distance v = some distance) :
    G.ReachableIn s v distance := by
  have hinv := bfsState_distanceInvariant G hs
  exact hinv.parentPath_reachableIn G (hinv.parentPath_of_distance G hdistance)

/-- Along any exact-length path from the source, the final BFS distance is no
larger than the path length. -/
theorem bfsState_distance_le_of_reachableIn {s v : V} (hs : s ∈ G.vertices)
    {length : Nat} (hpath : G.ReachableIn s v length) :
    ∃ distance, (bfsState G s hs).distance v = some distance ∧ distance ≤ length := by
  let result := bfsState G s hs
  have hinv : G.BFSDistanceInvariant s result := bfsState_distanceInvariant G hs
  have hqueue : result.queue = [] := bfsState_queue_empty G hs
  induction hpath with
  | refl => exact ⟨0, hinv.source_distance, le_rfl⟩
  | @tail u v n hprefix hadj ih =>
      rcases ih with ⟨du, hdu, hle⟩
      have hu_visited : u ∈ result.visited :=
        (hinv.distance_iff_visited u).2 ⟨du, hdu⟩
      have hv_visited : v ∈ result.visited :=
        hinv.closed u hu_visited (by simp [hqueue]) v hadj
      rcases (hinv.distance_iff_visited v).1 hv_visited with ⟨dv, hdv⟩
      have hdu' : result.distance u = some du := by simpa [result] using hdu
      have hu_level : result.level u = du := by simp [BFSState.level, hdu']
      have hv_level : result.level v = dv := by simp [BFSState.level, hdv]
      have hedge := hinv.processed_edge u hu_visited (by simp [hqueue]) v hadj
      rw [hu_level, hv_level] at hedge
      exact ⟨dv, hdv, by omega⟩

/-- Every present final BFS label is the unweighted shortest-path distance. -/
theorem bfsState_distance_isShortest {s v : V} (hs : s ∈ G.vertices)
    {distance : Nat} (hdistance : (bfsState G s hs).distance v = some distance) :
    G.IsShortestDistance s v distance := by
  constructor
  · exact bfsState_distance_reachableIn G hs hdistance
  · intro length hpath
    rcases bfsState_distance_le_of_reachableIn G hs hpath with ⟨d, hd, hle⟩
    rw [hdistance] at hd
    have : d = distance := (Option.some.inj hd).symm
    omega

/-- The final BFS distance map is defined exactly on reachable vertices. -/
theorem bfsState_distance_defined_iff_reachable {s v : V} (hs : s ∈ G.vertices) :
    (∃ distance, (bfsState G s hs).distance v = some distance) ↔ G.Reachable s v := by
  have hinv := bfsState_distanceInvariant G hs
  rw [← hinv.distance_iff_visited v, bfsState_visited_eq_bfs G hs]
  constructor
  · exact bfs_sound G hs
  · exact bfs_complete G hs

/-- Complete iff specification for the distance returned by CLRS BFS. -/
theorem bfsState_distance_eq_some_iff {s v : V} (hs : s ∈ G.vertices)
    {distance : Nat} :
    (bfsState G s hs).distance v = some distance ↔
      G.IsShortestDistance s v distance := by
  constructor
  · exact bfsState_distance_isShortest G hs
  · intro hshortest
    rcases (bfsState_distance_defined_iff_reachable G hs).2
        (hshortest.reachable G) with ⟨d, hd⟩
    have hd_shortest := bfsState_distance_isShortest G hs hd
    have h1 : distance ≤ d := hshortest.2 d hd_shortest.1
    have h2 : d ≤ distance := hd_shortest.2 distance hshortest.1
    have : d = distance := Nat.le_antisymm h2 h1
    simpa [this] using hd

-- =============================================================================
--  Predecessor-tree correctness
-- =============================================================================

/-- Every recorded predecessor is a graph edge and decreases BFS distance by
exactly one when followed toward the source. -/
theorem bfsState_parent_spec {s u v : V} (hs : s ∈ G.vertices)
    (hparent : (bfsState G s hs).parent v = some u) :
    G.Adj u v ∧ ∃ d,
      (bfsState G s hs).distance u = some d ∧
      (bfsState G s hs).distance v = some (d + 1) := by
  exact (bfsState_distanceInvariant G hs).parent_step u v hparent

/-- A non-source vertex has a predecessor exactly when it is reachable. -/
theorem bfsState_parent_defined_iff {s v : V} (hs : s ∈ G.vertices) :
    (∃ u, (bfsState G s hs).parent v = some u) ↔
      G.Reachable s v ∧ v ≠ s := by
  have hinv := bfsState_distanceInvariant G hs
  constructor
  · rintro ⟨u, hparent⟩
    rcases hinv.parent_step u v hparent with ⟨_, d, _, hdv⟩
    constructor
    · exact (bfsState_distance_reachableIn G hs hdv).reachable G
    · intro hvs
      subst v
      rw [hinv.source_parent] at hparent
      contradiction
  · rintro ⟨hreach, hvs⟩
    have hv_bfs : v ∈ bfs G s hs := bfs_complete G hs hreach
    have hv_visited : v ∈ (bfsState G s hs).visited := by
      rw [bfsState_visited_eq_bfs G hs]
      exact hv_bfs
    exact hinv.parent_exists v hv_visited hvs

/-- The root has no predecessor. -/
theorem bfsState_source_parent {s : V} (hs : s ∈ G.vertices) :
    (bfsState G s hs).parent s = none :=
  (bfsState_distanceInvariant G hs).source_parent

/-- The parent pointers recover a source-to-vertex path whose length is the
recorded distance. -/
theorem bfsState_parentPath {s v : V} (hs : s ∈ G.vertices) {distance : Nat}
    (hdistance : (bfsState G s hs).distance v = some distance) :
    BFSParentPath (bfsState G s hs).parent s v distance :=
  (bfsState_distanceInvariant G hs).parentPath_of_distance G hdistance

/-- Following a predecessor edge strictly increases level away from the root. -/
theorem bfsState_parent_level_lt {s u v : V} (hs : s ∈ G.vertices)
    (hparent : (bfsState G s hs).parent v = some u) :
    (bfsState G s hs).level u < (bfsState G s hs).level v := by
  rcases bfsState_parent_spec G hs hparent with ⟨_, d, hdu, hdv⟩
  simp [BFSState.level, hdu, hdv]

/-- The predecessor relation is acyclic. -/
theorem bfsState_parent_acyclic {s : V} (hs : s ∈ G.vertices) (v : V) :
    ¬Relation.TransGen
      (fun u w => (bfsState G s hs).parent w = some u) v v := by
  intro hcycle
  have hlt_of_trans : ∀ {a b},
      Relation.TransGen (fun u w => (bfsState G s hs).parent w = some u) a b →
        (bfsState G s hs).level a < (bfsState G s hs).level b := by
    intro a b h
    induction h with
    | single hparent => exact bfsState_parent_level_lt G hs hparent
    | tail _ hparent ih =>
        exact lt_trans ih (bfsState_parent_level_lt G hs hparent)
  have hlt := hlt_of_trans hcycle
  exact (Nat.lt_irrefl _ hlt)

/-- Specification of a rooted predecessor tree spanning precisely the vertices
reachable from {lit}`s`. -/
structure IsBFSPredecessorTree (G : Graph V) (s : V) (state : BFSState V) : Prop where
  root_parent : state.parent s = none
  parent_defined_iff : ∀ v, (∃ u, state.parent v = some u) ↔
    G.Reachable s v ∧ v ≠ s
  parent_edge : ∀ u v, state.parent v = some u → G.Adj u v
  parent_distance : ∀ u v, state.parent v = some u →
    ∃ d, state.distance u = some d ∧ state.distance v = some (d + 1)
  parent_path : ∀ v d, state.distance v = some d →
    BFSParentPath state.parent s v d
  acyclic : ∀ v, ¬Relation.TransGen (fun u w => state.parent w = some u) v v

/-- The parent pointers returned by CLRS BFS form a rooted predecessor tree on
all and only reachable vertices. -/
theorem bfsState_isBFSPredecessorTree {s : V} (hs : s ∈ G.vertices) :
    G.IsBFSPredecessorTree s (bfsState G s hs) := by
  refine {
    root_parent := bfsState_source_parent G hs
    parent_defined_iff := fun v => bfsState_parent_defined_iff G hs
    parent_edge := ?_
    parent_distance := ?_
    parent_path := ?_
    acyclic := bfsState_parent_acyclic G hs
  }
  · intro u v hparent
    exact (bfsState_parent_spec G hs hparent).1
  · intro u v hparent
    exact (bfsState_parent_spec G hs hparent).2
  · intro v d hd
    exact bfsState_parentPath G hs hd

/-- Combined shortest-distance and predecessor-tree specification. -/
def IsCorrectBFSState (G : Graph V) (s : V) (state : BFSState V) : Prop :=
  (∀ v d, state.distance v = some d ↔ G.IsShortestDistance s v d) ∧
    G.IsBFSPredecessorTree s state

/-- The labelled FIFO implementation satisfies the full CLRS BFS
specification. -/
theorem bfsState_correct {s : V} (hs : s ∈ G.vertices) :
    G.IsCorrectBFSState s (bfsState G s hs) := by
  constructor
  · intro v d
    exact bfsState_distance_eq_some_iff G hs
  · exact bfsState_isBFSPredecessorTree G hs

end Graph

end Chapter22
end CLRS
