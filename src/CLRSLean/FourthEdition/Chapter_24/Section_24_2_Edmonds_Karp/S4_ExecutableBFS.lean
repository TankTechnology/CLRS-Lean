import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S2_EK_Loop

/-!
# 24.2 S4. Executable breadth-first search

This module implements an executable breadth-first search over the residual
network of a flow `φ` and proves its correctness: the BFS distance labels are
the exact residual distances (`IsShortestDist`), the parent pointers walk back
to the source along residual edges, and the parent chain from the sink
assembles a shortest augmenting path whenever one exists.  This is the
executable core of the Edmonds-Karp loop: the augmenting path it computes can
be fed to `Flow.augment` in place of the classical choice used by `ekStep`
(see `ekStep_shortest_path_bfs`).

The search mirrors the Chapter 22 BFS state (`visited`, `queue`, `distance`,
`parent`), fuelled by the number of vertices; the queue invariants
(`BFSClosedInv`, `BFSQueueInv`, `BFSDistanceInvariant`) are the same, with
graph adjacency replaced by the residual relation `Flow.residualEdge φ`.

Main results:

- `residualBFS`: the fuelled breadth-first search over the residual network
- `residualBFS_distanceInvariant`: the distance/predecessor invariant holds
- `residualBFS_queue_empty`: the search exhausts its queue after `|V|` steps
- `bfsState_distance_eq_some_iff`: the BFS distance of a vertex is its
  residual shortest distance `IsShortestDist`
- `bfsParentResidualPath`: the parent chain from the sink assembles a simple
  residual path
- `bfs_shortestAugmenting`: an executable shortest augmenting path whenever
  one exists
- `ekStep_shortest_path_bfs`: the Edmonds-Karp step augments along a
  shortest path of the same length as the BFS path
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- The residual out-neighborhood of `u`: vertices reachable from `u` by one
residual edge. -/
noncomputable def residualAdj (φ : Flow V G) (u : V) : Finset V :=
  Finset.univ.filter (fun v => Flow.residualEdge φ u v)

@[simp]
theorem mem_residualAdj {φ : Flow V G} {u v : V} :
    v ∈ residualAdj φ u ↔ Flow.residualEdge φ u v := by
  simp [residualAdj]

/-- BFS state: discovered vertices, FIFO queue, distance labels, and parent
pointers.  A vertex is discovered exactly when it belongs to `visited`;
`distance` and `parent` record its first discovery. -/
structure BFSState (V : Type*) [DecidableEq V] where
  visited : Finset V
  queue : List V
  distance : V → Option ℕ
  parent : V → Option V

namespace BFSState

/-- Numeric level used by the queue invariants.  It is only inspected for
discovered vertices, where the distance is known to be present. -/
def level (state : BFSState V) (v : V) : ℕ :=
  (state.distance v).getD 0

end BFSState

/-- Initial BFS state at the source. -/
noncomputable def bfsStateInit (s : V) : BFSState V where
  visited := {s}
  queue := [s]
  distance := fun v => if v = s then some 0 else none
  parent := fun _ => none

/-- As-yet undiscovered residual out-neighbors of `u`. -/
noncomputable def bfsNewNeighbors (φ : Flow V G) (state : BFSState V) (u : V) : Finset V :=
  (residualAdj φ u).filter (fun v => v ∉ state.visited)

/-- Process the front vertex `u`, assigning distance `level u + 1` and parent
`u` to every newly discovered residual neighbor. -/
noncomputable def bfsStateAdvance (φ : Flow V G) (state : BFSState V)
    (u : V) (rest : List V) : BFSState V :=
  let newNeighbors := bfsNewNeighbors φ state u
  let nextDistance := state.level u + 1
  {
    visited := state.visited ∪ newNeighbors
    queue := rest ++ newNeighbors.toList
    distance := fun v =>
      if v ∈ newNeighbors then some nextDistance else state.distance v
    parent := fun v =>
      if v ∈ newNeighbors then some u else state.parent v
  }

/-- Fuelled residual BFS. -/
noncomputable def bfsStateAux (φ : Flow V G) : ℕ → BFSState V → BFSState V
  | 0, state => state
  | fuel + 1, state =>
      match state.queue with
      | [] => state
      | u :: rest => bfsStateAux φ fuel (bfsStateAdvance φ state u rest)

/-- BFS over the residual network of `φ`, fuelled by the number of vertices. -/
noncomputable def residualBFS (φ : Flow V G) : BFSState V :=
  bfsStateAux φ (Fintype.card V) (bfsStateInit G.s)

/-- Closure invariant: every neighbor of a processed (no longer queued)
vertex is already visited. -/
def BFSClosedInv (φ : Flow V G) (visited : Finset V) (queue : List V) : Prop :=
  ∀ u ∈ visited, u ∉ queue → ∀ v, Flow.residualEdge φ u v → v ∈ visited

/-- Queue invariant: every queued vertex is already marked visited. -/
def BFSQueueInv (φ : Flow V G) (visited : Finset V) (queue : List V) : Prop :=
  ∀ v ∈ queue, v ∈ visited

theorem mem_bfsNewNeighbors_iff {φ : Flow V G} {state : BFSState V} {u v : V} :
    v ∈ bfsNewNeighbors φ state u ↔ Flow.residualEdge φ u v ∧ v ∉ state.visited := by
  simp [bfsNewNeighbors]

/-- The closure invariant is preserved by one BFS step. -/
theorem bfsClosedInv_step {φ : Flow V G} {u : V} {rest : List V} {visited : Finset V}
    (hclosed : BFSClosedInv φ visited (u :: rest)) :
    BFSClosedInv φ
      (visited ∪ (residualAdj φ u).filter (fun v => v ∉ visited))
      (rest ++ ((residualAdj φ u).filter (fun v => v ∉ visited)).toList) := by
  intro x hx hxnotin v hvx
  simp [BFSClosedInv] at hclosed
  simp [Finset.mem_union, Finset.mem_filter] at hx
  rcases hx with (hx | ⟨hxadj, hxnvis⟩)
  · by_cases hxu : x = u
    · rw [hxu] at hvx
      by_cases h : v ∈ visited
      · simp [h]
      · simp [h, hvx]
    · by_cases hxrest : x ∈ rest
      · exfalso
        simp [hxrest] at hxnotin
      · have hxnotin' : x ∉ u :: rest := by
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
  · exfalso
    have : x ∈ rest ++ ((residualAdj φ u).filter (fun v => v ∉ visited)).toList := by
      simp [hxadj, hxnvis]
    contradiction

/-- The queue invariant is preserved by one BFS step. -/
theorem bfsQueueInv_step {φ : Flow V G} {u : V} {rest : List V} {visited : Finset V}
    (hqueue : BFSQueueInv φ visited (u :: rest)) :
    BFSQueueInv φ
      (visited ∪ (residualAdj φ u).filter (fun v => v ∉ visited))
      (rest ++ ((residualAdj φ u).filter (fun v => v ∉ visited)).toList) := by
  intro x hx
  simp [BFSQueueInv] at hqueue
  rcases hqueue with ⟨hu, hrest⟩
  simp [List.mem_append, Finset.mem_toList, Finset.mem_filter] at hx
  rcases hx with (hx | ⟨hxadj, hxnvis⟩)
  · have : x ∈ visited := hrest x hx
    simp [this]
  · simp [hxadj, hxnvis]

/-- Invariant connecting the FIFO search state to CLRS distance and predecessor
labels.  The queue is ordered by nondecreasing level and spans at most two
consecutive levels; processed edges already satisfy the shortest-path upper
bound needed at termination. -/
structure BFSDistanceInvariant (φ : Flow V G) (s : V) (state : BFSState V) : Prop where
  closed : BFSClosedInv φ state.visited state.queue
  queued : BFSQueueInv φ state.visited state.queue
  source_distance : state.distance s = some 0
  source_parent : state.parent s = none
  distance_iff_visited : ∀ v, v ∈ state.visited ↔ ∃ d, state.distance v = some d
  distance_zero : ∀ v, state.distance v = some 0 → v = s
  parent_exists : ∀ v, v ∈ state.visited → v ≠ s → ∃ u, state.parent v = some u
  parent_unvisited : ∀ v, v ∉ state.visited → state.parent v = none
  parent_step : ∀ u v, state.parent v = some u →
    Flow.residualEdge φ u v ∧ ∃ d, state.distance u = some d ∧ state.distance v = some (d + 1)
  queue_ordered : state.queue.Pairwise (fun u v => state.level u ≤ state.level v)
  visited_span : ∀ u rest, state.queue = u :: rest →
    ∀ v ∈ state.visited, state.level v ≤ state.level u + 1
  processed_edge : ∀ u ∈ state.visited, u ∉ state.queue →
    ∀ v, Flow.residualEdge φ u v → state.level v ≤ state.level u + 1

/-- Processing a vertex does not change labels of already discovered vertices. -/
theorem bfsStateAdvance_distance_of_visited {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance φ state u rest).distance v = state.distance v := by
  have hvnew : v ∉ bfsNewNeighbors φ state u := by
    simp [mem_bfsNewNeighbors_iff, hv]
  simp [bfsStateAdvance, hvnew]

theorem bfsStateAdvance_parent_of_visited {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance φ state u rest).parent v = state.parent v := by
  have hvnew : v ∉ bfsNewNeighbors φ state u := by
    simp [mem_bfsNewNeighbors_iff, hv]
  simp [bfsStateAdvance, hvnew]

theorem bfsStateAdvance_level_of_visited {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ state.visited) :
    (bfsStateAdvance φ state u rest).level v = state.level v := by
  simp [BFSState.level, bfsStateAdvance_distance_of_visited (φ := φ) hv]

/-- Every newly discovered vertex receives the front vertex's level plus one
and records the front vertex as its parent. -/
theorem bfsStateAdvance_distance_of_new {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors φ state u) :
    (bfsStateAdvance φ state u rest).distance v = some (state.level u + 1) := by
  simp [bfsStateAdvance, hv]

theorem bfsStateAdvance_parent_of_new {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors φ state u) :
    (bfsStateAdvance φ state u rest).parent v = some u := by
  simp [bfsStateAdvance, hv]

theorem bfsStateAdvance_level_of_new {φ : Flow V G} {state : BFSState V} {u v : V}
    {rest : List V} (hv : v ∈ bfsNewNeighbors φ state u) :
    (bfsStateAdvance φ state u rest).level v = state.level u + 1 := by
  simp [BFSState.level, bfsStateAdvance_distance_of_new (φ := φ) hv]

/-- The initial labelled state satisfies all distance and predecessor
invariants. -/
theorem bfsDistanceInvariant_init (φ : Flow V G) (s : V) :
    BFSDistanceInvariant φ s (bfsStateInit s) := by
  constructor <;> simp [BFSClosedInv, BFSQueueInv, bfsStateInit, BFSState.level]

/-- One FIFO step preserves the distance and predecessor invariant. -/
theorem bfsDistanceInvariant_step {φ : Flow V G} {s u : V} {rest : List V} {state : BFSState V}
    (hqueue : state.queue = u :: rest)
    (hinv : BFSDistanceInvariant φ s state) :
    BFSDistanceInvariant φ s (bfsStateAdvance φ state u rest) := by
  have hu_queue : u ∈ state.queue := by simp [hqueue]
  have hu_visited : u ∈ state.visited := hinv.queued u hu_queue
  have hu_not_new : u ∉ bfsNewNeighbors φ state u := by
    simp [mem_bfsNewNeighbors_iff, hu_visited]
  have hclosed : BFSClosedInv φ state.visited (u :: rest) := by
    simpa [hqueue] using hinv.closed
  have hqueued : BFSQueueInv φ state.visited (u :: rest) := by
    simpa [hqueue] using hinv.queued
  have hs_visited : s ∈ state.visited :=
    (hinv.distance_iff_visited s).2 ⟨0, hinv.source_distance⟩
  have hs_not_new : s ∉ bfsNewNeighbors φ state u := by
    simp [mem_bfsNewNeighbors_iff, hs_visited]
  have hordered : (u :: rest).Pairwise
      (fun a b => state.level a ≤ state.level b) := by
    simpa [hqueue] using hinv.queue_ordered
  constructor
  · simpa [bfsStateAdvance, bfsNewNeighbors] using
      (bfsClosedInv_step (φ := φ) hclosed)
  · simpa [bfsStateAdvance, bfsNewNeighbors] using
      (bfsQueueInv_step (φ := φ) hqueued)
  · simpa [bfsStateAdvance, hs_not_new] using hinv.source_distance
  · simpa [bfsStateAdvance, hs_not_new] using hinv.source_parent
  · intro v
    constructor
    · intro hv
      change v ∈ state.visited ∪ bfsNewNeighbors φ state u at hv
      rcases Finset.mem_union.mp hv with hvold | hvnew
      · rcases (hinv.distance_iff_visited v).1 hvold with ⟨d, hd⟩
        exact ⟨d, by simpa [bfsStateAdvance_distance_of_visited (φ := φ) hvold] using hd⟩
      · exact ⟨state.level u + 1, bfsStateAdvance_distance_of_new (φ := φ) hvnew⟩
    · rintro ⟨d, hd⟩
      by_cases hvnew : v ∈ bfsNewNeighbors φ state u
      · exact Finset.mem_union_right _ hvnew
      · have hdold : state.distance v = some d := by
          simpa [bfsStateAdvance, hvnew] using hd
        exact Finset.mem_union_left _ ((hinv.distance_iff_visited v).2 ⟨d, hdold⟩)
  · intro v hvzero
    by_cases hvnew : v ∈ bfsNewNeighbors φ state u
    · have := bfsStateAdvance_distance_of_new (φ := φ) (rest := rest) hvnew
      rw [hvzero] at this
      simp at this
    · have hvold : state.distance v = some 0 := by
        simpa [bfsStateAdvance, hvnew] using hvzero
      exact hinv.distance_zero v hvold
  · intro v hv hvs
    change v ∈ state.visited ∪ bfsNewNeighbors φ state u at hv
    rcases Finset.mem_union.mp hv with hvold | hvnew
    · rcases hinv.parent_exists v hvold hvs with ⟨p, hp⟩
      exact ⟨p, by simpa [bfsStateAdvance_parent_of_visited (φ := φ) hvold] using hp⟩
    · exact ⟨u, bfsStateAdvance_parent_of_new (φ := φ) hvnew⟩
  · intro v hv
    have hvold : v ∉ state.visited := by
      intro h
      exact hv (Finset.mem_union_left _ h)
    have hvnew : v ∉ bfsNewNeighbors φ state u := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    simpa [bfsStateAdvance, hvnew] using hinv.parent_unvisited v hvold
  · intro p v hp
    by_cases hvnew : v ∈ bfsNewNeighbors φ state u
    · have hp_eq : p = u := by
        have hnewParent := bfsStateAdvance_parent_of_new (φ := φ) (rest := rest) hvnew
        rw [hp] at hnewParent
        exact Option.some.inj hnewParent
      subst p
      have hadj : Flow.residualEdge φ u v := (mem_bfsNewNeighbors_iff (φ := φ)).1 hvnew |>.1
      rcases (hinv.distance_iff_visited u).1 hu_visited with ⟨d, hd⟩
      have hlevel : state.level u = d := by simp [BFSState.level, hd]
      refine ⟨hadj, d, ?_, ?_⟩
      simpa [bfsStateAdvance_distance_of_visited (φ := φ) hu_visited] using hd
      simpa [hlevel] using bfsStateAdvance_distance_of_new (φ := φ) (rest := rest) hvnew
    · have hpold : state.parent v = some p := by
        simpa [bfsStateAdvance, hvnew] using hp
      rcases hinv.parent_step p v hpold with ⟨hadj, d, hdp, hdv⟩
      have hp_visited : p ∈ state.visited :=
        (hinv.distance_iff_visited p).2 ⟨d, hdp⟩
      have hv_visited : v ∈ state.visited :=
        (hinv.distance_iff_visited v).2 ⟨d + 1, hdv⟩
      refine ⟨hadj, d, ?_, ?_⟩
      · simpa [bfsStateAdvance_distance_of_visited (φ := φ) hp_visited] using hdp
      · simpa [bfsStateAdvance_distance_of_visited (φ := φ) hv_visited] using hdv
  · change (rest ++ (bfsNewNeighbors φ state u).toList).Pairwise
      (fun a b => (bfsStateAdvance φ state u rest).level a ≤
        (bfsStateAdvance φ state u rest).level b)
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · have hrest := hordered.tail
      rw [List.pairwise_iff_get] at hrest ⊢
      intro i j hij
      have hi_visited : rest.get i ∈ state.visited := hqueued _ (by simp)
      have hj_visited : rest.get j ∈ state.visited := hqueued _ (by simp)
      rw [bfsStateAdvance_level_of_visited (φ := φ) (rest := rest) hi_visited,
        bfsStateAdvance_level_of_visited (φ := φ) (rest := rest) hj_visited]
      exact hrest i j hij
    · apply List.pairwise_of_reflexive_of_forall_ne
      intro a ha b hb _
      have ha_new : a ∈ bfsNewNeighbors φ state u := Finset.mem_toList.mp ha
      have hb_new : b ∈ bfsNewNeighbors φ state u := Finset.mem_toList.mp hb
      rw [bfsStateAdvance_level_of_new (φ := φ) ha_new,
        bfsStateAdvance_level_of_new (φ := φ) hb_new]
    · intro a ha b hb
      have ha_visited : a ∈ state.visited := hqueued a (by simp [ha])
      have hb_new : b ∈ bfsNewNeighbors φ state u := Finset.mem_toList.mp hb
      rw [bfsStateAdvance_level_of_visited (φ := φ) ha_visited,
        bfsStateAdvance_level_of_new (φ := φ) hb_new]
      exact hinv.visited_span u rest hqueue a ha_visited
  · intro front tail hnext_queue v hv
    have hv_union : v ∈ state.visited ∪ bfsNewNeighbors φ state u := by
      simpa [bfsStateAdvance] using hv
    have hv_bound : (bfsStateAdvance φ state u rest).level v ≤ state.level u + 1 := by
      rcases Finset.mem_union.mp hv_union with hvold | hvnew
      · rw [bfsStateAdvance_level_of_visited (φ := φ) hvold]
        exact hinv.visited_span u rest hqueue v hvold
      · rw [bfsStateAdvance_level_of_new (φ := φ) hvnew]
    cases rest with
    | nil =>
        have hlist : (bfsNewNeighbors φ state u).toList = front :: tail := by
          simpa [bfsStateAdvance] using hnext_queue
        have hfront_new : front ∈ bfsNewNeighbors φ state u := by
          apply Finset.mem_toList.mp
          rw [hlist]
          simp
        rw [bfsStateAdvance_level_of_new (φ := φ) hfront_new]
        omega
    | cons next remaining =>
        have hlist : next :: (remaining ++ (bfsNewNeighbors φ state u).toList) =
            front :: tail := by
          simpa [bfsStateAdvance] using hnext_queue
        have hfront : front = next := by
          injection hlist with hhead _
          exact hhead.symm
        subst front
        have hnext_visited : next ∈ state.visited := hqueued next (by simp)
        have hu_le_next : state.level u ≤ state.level next :=
          List.rel_of_pairwise_cons hordered (by simp)
        rw [bfsStateAdvance_level_of_visited (φ := φ) hnext_visited]
        omega
  · intro x hx hnotin y hxy
    have hx_union : x ∈ state.visited ∪ bfsNewNeighbors φ state u := by
      simpa [bfsStateAdvance] using hx
    rcases Finset.mem_union.mp hx_union with hxold | hxnew
    · by_cases hxu : x = u
      · subst x
        by_cases hyold : y ∈ state.visited
        · rw [bfsStateAdvance_level_of_visited (φ := φ) hyold,
            bfsStateAdvance_level_of_visited (φ := φ) hu_visited]
          exact hinv.visited_span u rest hqueue y hyold
        · have hynew : y ∈ bfsNewNeighbors φ state u :=
            (mem_bfsNewNeighbors_iff (φ := φ)).2 ⟨hxy, hyold⟩
          rw [bfsStateAdvance_level_of_new (φ := φ) hynew,
            bfsStateAdvance_level_of_visited (φ := φ) hu_visited]
      · have hx_not_rest : x ∉ rest := by
          intro hxrest
          apply hnotin
          change x ∈ rest ++ (bfsNewNeighbors φ state u).toList
          exact List.mem_append_left _ hxrest
        have hx_not_queue : x ∉ state.queue := by
          rw [hqueue]
          simp [hxu, hx_not_rest]
        have hyold : y ∈ state.visited := hclosed x hxold (by
          simp [hxu, hx_not_rest]) y hxy
        rw [bfsStateAdvance_level_of_visited (φ := φ) hyold,
          bfsStateAdvance_level_of_visited (φ := φ) hxold]
        exact hinv.processed_edge x hxold hx_not_queue y hxy
    · exfalso
      apply hnotin
      change x ∈ rest ++ (bfsNewNeighbors φ state u).toList
      exact List.mem_append_right _ (Finset.mem_toList.mpr hxnew)

/-- Every fuelled execution preserves the distance invariant. -/
theorem bfsDistanceInvariant_aux {φ : Flow V G} {s : V} (fuel : ℕ) (state : BFSState V)
    (hinv : BFSDistanceInvariant φ s state) :
    BFSDistanceInvariant φ s (bfsStateAux φ fuel state) := by
  induction fuel generalizing state with
  | zero => simpa [bfsStateAux]
  | succ fuel ih =>
      cases hqueue : state.queue with
      | nil => simpa [bfsStateAux, hqueue]
      | cons u rest =>
          simp only [bfsStateAux, hqueue]
          exact ih (bfsStateAdvance φ state u rest)
            (bfsDistanceInvariant_step (φ := φ) hqueue hinv)

/-- The final residual BFS state satisfies the distance invariant. -/
theorem residualBFS_distanceInvariant (φ : Flow V G) :
    BFSDistanceInvariant φ G.s (residualBFS φ) := by
  simpa [residualBFS] using
    (bfsDistanceInvariant_aux (φ := φ) (Fintype.card V) (bfsStateInit G.s)
      (bfsDistanceInvariant_init φ G.s))

/-- The BFS measure: unvisited vertices plus queue length.  Every step with a
nonempty queue decreases it by exactly one, and it starts at `|V|`. -/
def bfsMeasure (state : BFSState V) : ℕ :=
  (Finset.univ \ state.visited).card + state.queue.length

/-- Processing the front vertex decreases the measure by exactly one. -/
theorem bfsStateAdvance_measure {φ : Flow V G} {state : BFSState V} {u : V} {rest : List V} :
    bfsMeasure (bfsStateAdvance φ state u rest) + 1 =
      bfsMeasure {state with queue := u :: rest} := by
  unfold bfsMeasure bfsStateAdvance
  have hnew_sub : bfsNewNeighbors φ state u ⊆ Finset.univ \ state.visited := by
    intro x hx
    simp [Finset.mem_sdiff]
    exact (Finset.mem_filter.mp hx).2
  have hcard : (Finset.univ \ (state.visited ∪ bfsNewNeighbors φ state u)).card =
      (Finset.univ \ state.visited).card - (bfsNewNeighbors φ state u).card := by
    have hset : Finset.univ \ (state.visited ∪ bfsNewNeighbors φ state u) =
        (Finset.univ \ state.visited) \ bfsNewNeighbors φ state u := by
      ext x
      simp [Finset.mem_sdiff]
    have hEq : bfsNewNeighbors φ state u ∩ (Finset.univ \ state.visited) =
        bfsNewNeighbors φ state u := by
      exact Finset.inter_eq_left.mpr hnew_sub
    rw [hset, Finset.card_sdiff, hEq]
  have hle : (bfsNewNeighbors φ state u).card ≤
      (Finset.univ \ state.visited).card :=
    Finset.card_le_card hnew_sub
  simp [hcard]
  omega

/-- If the queue is nonempty throughout, the measure drops by exactly one per
step. -/
theorem bfsStateAux_measure_of_nonempty {φ : Flow V G} (fuel : ℕ) (state : BFSState V)
    (h : (bfsStateAux φ fuel state).queue ≠ []) :
    bfsMeasure (bfsStateAux φ fuel state) = bfsMeasure state - fuel := by
  refine Nat.rec
    (motive := fun fuel => ∀ state : BFSState V,
      (bfsStateAux φ fuel state).queue ≠ [] →
        bfsMeasure (bfsStateAux φ fuel state) = bfsMeasure state - fuel)
    ?_ ?_ fuel state h
  · intro state h
    simp [bfsStateAux]
  · intro fuel ih state h
    cases hqueue : state.queue with
    | nil =>
        have hnil : (bfsStateAux φ (fuel + 1) state).queue = [] := by
          simp [bfsStateAux, hqueue]
        exact (h hnil).elim
    | cons u rest =>
        have h' : (bfsStateAux φ fuel (bfsStateAdvance φ state u rest)).queue ≠ [] := by
          simpa [bfsStateAux, hqueue] using h
        have hih := ih (bfsStateAdvance φ state u rest) h'
        have hdec' : bfsMeasure (bfsStateAdvance φ state u rest) = bfsMeasure state - 1 := by
          have hdec := bfsStateAdvance_measure (φ := φ) (state := state) (u := u)
            (rest := rest)
          have hEq : bfsMeasure {state with queue := u :: rest} = bfsMeasure state := by
            unfold bfsMeasure
            simp [hqueue]
          omega
        have hmeas : bfsMeasure (bfsStateAux φ fuel (bfsStateAdvance φ state u rest)) =
            bfsMeasure state - (fuel + 1) := by
          rw [hih, hdec']
          omega
        simpa [bfsStateAux, hqueue] using hmeas

/-- The fuelled residual BFS exhausts its queue: after `|V|` steps every
vertex reachable in the residual network has been discovered. -/
theorem residualBFS_queue_empty (φ : Flow V G) : (residualBFS φ).queue = [] := by
  by_contra h
  have hmeas := bfsStateAux_measure_of_nonempty (φ := φ) (fuel := Fintype.card V)
    (state := bfsStateInit G.s) h
  have hinit : bfsMeasure (bfsStateInit G.s) = Fintype.card V := by
    change (Finset.univ \ ({G.s} : Finset V)).card + ([G.s] : List V).length =
      Fintype.card V
    simp
    have hpos : 0 < Fintype.card V := Fintype.card_pos (α := V) (h := ⟨G.s⟩)
    have hcard : (Finset.univ \ ({G.s} : Finset V)).card = Fintype.card V - 1 := by
      rw [Finset.sdiff_singleton_eq_erase]
      exact Finset.card_erase_of_mem (Finset.mem_univ G.s)
    rw [hcard]
    omega
  have hzero : bfsMeasure (residualBFS φ) = 0 := by
    unfold residualBFS
    rw [hmeas, hinit]
    omega
  have hge : 1 ≤ bfsMeasure (residualBFS φ) := by
    unfold bfsMeasure
    have hlen : 1 ≤ (residualBFS φ).queue.length := List.length_pos_iff.mpr h
    omega
  omega

/-- A path following the recorded parent function from the source.  This is a
`Type` rather than a `Prop` so that its vertex list can be extracted by
pattern matching (see `BFSParentPath.vertices`). -/
inductive BFSParentPath (parent : V → Option V) (s : V) : V → ℕ → Type _ where
  | root : BFSParentPath parent s s 0
  | tail {u v : V} {n : ℕ} :
      BFSParentPath parent s u n → parent v = some u →
        BFSParentPath parent s v (n + 1)

/-- Every distance label maintained by the invariant is witnessed by a parent
path of exactly that length. -/
noncomputable def BFSDistanceInvariant.parentPath_of_distance
    {φ : Flow V G} {s : V} {state : BFSState V} (hinv : BFSDistanceInvariant φ s state)
    {v : V} {d : ℕ} (hd : state.distance v = some d) :
    BFSParentPath state.parent s v d := by
  refine (inferInstance : IsWellFounded ℕ (· < ·)).wf.fix
    (C := fun n => ∀ v (hd : state.distance v = some n),
      BFSParentPath state.parent s v n) ?_ d v hd
  intro n ih v hd
  cases n with
  | zero =>
      have hvs : v = s := hinv.distance_zero v hd
      subst v
      exact BFSParentPath.root
  | succ n =>
      have hv_visited : v ∈ state.visited :=
        (hinv.distance_iff_visited v).2 ⟨n + 1, hd⟩
      have hvs : v ≠ s := by
        intro h
        subst v
        rw [hinv.source_distance] at hd
        simp at hd
      have hu' : ∃ u, state.parent v = some u := hinv.parent_exists v hv_visited hvs
      let u := Classical.choose hu'
      have hparent : state.parent v = some u := Classical.choose_spec hu'
      have hstep := hinv.parent_step u v hparent
      have hdv' : ∃ d, state.distance u = some d ∧ state.distance v = some (d + 1) := hstep.2
      let d' := Classical.choose hdv'
      have hdu : state.distance u = some d' := (Classical.choose_spec hdv').1
      have hdv : state.distance v = some (d' + 1) := (Classical.choose_spec hdv').2
      have hdn : d' = n := by
        rw [hd] at hdv
        simp at hdv
        omega
      have hdu'' : state.distance u = some n := by
        simpa [hdn] using hdu
      exact BFSParentPath.tail (ih n (by omega) u hdu'') hparent

/-- Parent paths in a valid BFS state are residual paths with the same number
of edges. -/
theorem BFSDistanceInvariant.parentPath_ResidualPathLength
    {φ : Flow V G} {s : V} {state : BFSState V} (hinv : BFSDistanceInvariant φ s state)
    {v : V} {d : ℕ} (hpath : BFSParentPath state.parent s v d) :
    ResidualPathLength φ s v d := by
  induction hpath with
  | root => exact ResidualPathLength.refl s
  | @tail u v n hpath hparent ih =>
      exact ResidualPathLength.tail s u v n ih (hinv.parent_step u v hparent).1

/-- Exact-length reachability in the residual network implies residual
reachability. -/
lemma ResidualPathLength.reachable {φ : Flow V G} {u v : V} {n : ℕ}
    (h : ResidualPathLength φ u v n) : Flow.augmentingPathReachable φ u v := by
  refine ResidualPathLength.rec
    (motive := fun (v : V) (n : ℕ) (_h : ResidualPathLength φ u v n) =>
      Flow.augmentingPathReachable φ u v)
    (by exact Relation.ReflTransGen.refl)
    (fun v w n hprev hedge ih => Relation.ReflTransGen.tail ih hedge)
    h

/-- Every recorded distance is attained by a residual path of exactly that
length. -/
theorem bfsState_distance_ResidualPathLength (φ : Flow V G) {v : V} {d : ℕ}
    (hd : (residualBFS φ).distance v = some d) :
    ResidualPathLength φ G.s v d := by
  have hinv := residualBFS_distanceInvariant φ
  exact hinv.parentPath_ResidualPathLength (hinv.parentPath_of_distance hd)

/-- Along any exact-length residual path from the source, the final BFS
distance is no larger than the path length. -/
theorem bfsState_distance_le_of_ResidualPathLength (φ : Flow V G) {v : V} {n : ℕ}
    (hpath : ResidualPathLength φ G.s v n) :
    ∃ d, (residualBFS φ).distance v = some d ∧ d ≤ n := by
  let result := residualBFS φ
  have hinv : BFSDistanceInvariant φ G.s result := residualBFS_distanceInvariant φ
  have hqueue : result.queue = [] := residualBFS_queue_empty φ
  have h := ResidualPathLength.rec
    (motive := fun (v : V) (n : ℕ) (_h : ResidualPathLength φ G.s v n) =>
      ∃ d, result.distance v = some d ∧ d ≤ n)
    (by exact ⟨0, hinv.source_distance, le_rfl⟩)
    (fun v w n hprev hedge ih => by
      rcases ih with ⟨dv, hdv, hle⟩
      have hv_visited : v ∈ result.visited :=
        (hinv.distance_iff_visited v).2 ⟨dv, hdv⟩
      have hw_visited : w ∈ result.visited :=
        hinv.closed v hv_visited (by simp [hqueue]) w hedge
      rcases (hinv.distance_iff_visited w).1 hw_visited with ⟨dw, hdw⟩
      have hdv' : result.distance v = some dv := by simpa [result] using hdv
      have hv_level : result.level v = dv := by simp [BFSState.level, hdv']
      have hw_level : result.level w = dw := by simp [BFSState.level, hdw]
      have hedge' := hinv.processed_edge v hv_visited (by simp [hqueue]) w hedge
      rw [hv_level, hw_level] at hedge'
      exact ⟨dw, hdw, by omega⟩)
    hpath
  simpa [result] using h

/-- Every present final BFS label is the residual shortest-path distance. -/
theorem bfsState_distance_isShortest (φ : Flow V G) {v : V} {d : ℕ}
    (hd : (residualBFS φ).distance v = some d) :
    IsShortestDist φ G.s v d := by
  constructor
  · exact bfsState_distance_ResidualPathLength φ hd
  · intro n hn
    rcases bfsState_distance_le_of_ResidualPathLength φ hn with ⟨d', hd', hle⟩
    rw [hd] at hd'
    have : d' = d := (Option.some.inj hd').symm
    omega

/-- BFS discovers exactly the residual-reachable vertices. -/
theorem residualBFS_visited_iff_reachable (φ : Flow V G) (v : V) :
    v ∈ (residualBFS φ).visited ↔ Flow.augmentingPathReachable φ G.s v := by
  let result := residualBFS φ
  have hinv : BFSDistanceInvariant φ G.s result := residualBFS_distanceInvariant φ
  have hqueue : result.queue = [] := residualBFS_queue_empty φ
  constructor
  · intro hv
    rcases (hinv.distance_iff_visited v).1 hv with ⟨d, hd⟩
    exact (bfsState_distance_ResidualPathLength φ hd).reachable
  · intro hreach
    induction hreach with
    | refl =>
        exact (hinv.distance_iff_visited G.s).2 ⟨0, hinv.source_distance⟩
    | tail hprev hedge ih =>
        exact hinv.closed _ ih (by simp [hqueue]) _ hedge

/-- The final BFS distance map is defined exactly on reachable vertices. -/
theorem bfsState_distance_defined_iff_reachable (φ : Flow V G) (v : V) :
    (∃ d, (residualBFS φ).distance v = some d) ↔ Flow.augmentingPathReachable φ G.s v := by
  let result := residualBFS φ
  have hinv : BFSDistanceInvariant φ G.s result := residualBFS_distanceInvariant φ
  constructor
  · rintro ⟨d, hd⟩
    exact (bfsState_distance_ResidualPathLength φ hd).reachable
  · intro hreach
    have hv_visited : v ∈ result.visited :=
      (residualBFS_visited_iff_reachable φ v).2 hreach
    simpa [result] using (hinv.distance_iff_visited v).1 hv_visited

/-- Complete iff specification for the distance returned by residual BFS. -/
theorem bfsState_distance_eq_some_iff (φ : Flow V G) (v : V) {d : ℕ} :
    (residualBFS φ).distance v = some d ↔ IsShortestDist φ G.s v d := by
  constructor
  · exact bfsState_distance_isShortest φ
  · intro hshortest
    rcases (bfsState_distance_defined_iff_reachable φ v).2 hshortest.1.reachable with ⟨d', hd'⟩
    have hd'_shortest := bfsState_distance_isShortest φ hd'
    have h1 : d ≤ d' := hshortest.2 d' hd'_shortest.1
    have h2 : d' ≤ d := hd'_shortest.2 d hshortest.1
    have : d' = d := Nat.le_antisymm h2 h1
    simpa [this] using hd'

/-- Every recorded predecessor is a residual edge and decreases BFS distance
by exactly one when followed toward the source. -/
theorem bfsState_parent_spec (φ : Flow V G) {u v : V}
    (hparent : (residualBFS φ).parent v = some u) :
    Flow.residualEdge φ u v ∧ ∃ d,
      (residualBFS φ).distance u = some d ∧
      (residualBFS φ).distance v = some (d + 1) := by
  exact (residualBFS_distanceInvariant φ).parent_step u v hparent

/-- Following a predecessor edge strictly increases level away from the root. -/
theorem bfsState_parent_level_lt (φ : Flow V G) {u v : V}
    (hparent : (residualBFS φ).parent v = some u) :
    (residualBFS φ).level u < (residualBFS φ).level v := by
  rcases bfsState_parent_spec φ hparent with ⟨_, d, hdu, hdv⟩
  simp [BFSState.level, hdu, hdv]

/-- The vertices of a parent path, from the source to the endpoint. -/
noncomputable def BFSParentPath.vertices {parent : V → Option V} {s v : V} {n : ℕ}
    (h : BFSParentPath parent s v n) : List V :=
  match h with
  | root => [s]
  | tail hprev _ => BFSParentPath.vertices hprev ++ [v]

/-- The parent path has exactly `n + 1` vertices. -/
lemma BFSParentPath.vertices_length {parent : V → Option V} {s v : V} {n : ℕ}
    (h : BFSParentPath parent s v n) : (BFSParentPath.vertices h).length = n + 1 := by
  induction h with
  | root => simp [BFSParentPath.vertices]
  | tail hprev _ ih =>
      simp [BFSParentPath.vertices, ih]

/-- The parent path starts at the source. -/
lemma BFSParentPath.vertices_head {parent : V → Option V} {s v : V} {n : ℕ}
    (h : BFSParentPath parent s v n) : (BFSParentPath.vertices h).head? = some s := by
  induction h with
  | root => simp [BFSParentPath.vertices]
  | @tail u v n hprev _ ih =>
      have hne : BFSParentPath.vertices hprev ≠ [] := by
        rw [← List.length_pos_iff, BFSParentPath.vertices_length]
        omega
      rw [BFSParentPath.vertices]
      rw [List.head?_append_of_ne_nil _ hne]
      exact ih

/-- The parent path ends at the requested vertex. -/
lemma BFSParentPath.vertices_getLast {parent : V → Option V} {s v : V} {n : ℕ}
    (h : BFSParentPath parent s v n) : (BFSParentPath.vertices h).getLast? = some v := by
  induction h with
  | root => simp [BFSParentPath.vertices]
  | @tail u v n hprev _ ih =>
      rw [BFSParentPath.vertices]
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
      rfl

/-- Consecutive vertices of a parent path are joined by residual edges. -/
lemma BFSParentPath.vertices_chain {φ : Flow V G} {s : V} {state : BFSState V}
    (hinv : BFSDistanceInvariant φ s state) {v : V} {n : ℕ}
    (h : BFSParentPath state.parent s v n) :
    (BFSParentPath.vertices h).IsChain (Flow.residualEdge φ) := by
  induction h with
  | root => simp [BFSParentPath.vertices]
  | @tail u v n hprev hpar ih =>
      rw [BFSParentPath.vertices]
      apply IsChain_append_last
      · exact ih
      · intro y hy
        have hlast := hprev.vertices_getLast
        have hyu : y = u := by
          have : u = y := by simpa [hlast] using hy
          exact this.symm
        simpa [hyu] using (hinv.parent_step u v hpar).1

/-- The vertex at position `i` of a parent path has BFS level exactly `i`. -/
lemma BFSParentPath.vertices_level_getElem {φ : Flow V G} {s : V} {state : BFSState V}
    (hinv : BFSDistanceInvariant φ s state) {v : V} {n : ℕ}
    (h : BFSParentPath state.parent s v n) :
    ∀ i (hi : i < (BFSParentPath.vertices h).length),
      state.level (BFSParentPath.vertices h)[i] = i := by
  induction h with
  | root =>
      intro i hi
      have hi0 : i = 0 := by
        simp [BFSParentPath.vertices] at hi
        exact hi
      subst i
      simp [BFSParentPath.vertices, BFSState.level, hinv.source_distance]
  | @tail u v n hprev hpar ih =>
      intro i hi
      by_cases hi_lt : i < (BFSParentPath.vertices hprev).length
      · have hget : (BFSParentPath.vertices hprev ++ [v])[i] =
            (BFSParentPath.vertices hprev)[i] :=
          List.getElem_append_left hi_lt
        have hle := ih i hi_lt
        change state.level ((BFSParentPath.vertices hprev ++ [v])[i]) = i
        rw [hget]
        exact hle
      · have hi_eq : i = (BFSParentPath.vertices hprev).length := by
          simp [BFSParentPath.vertices] at hi
          omega
        subst i
        have hget : (BFSParentPath.vertices hprev ++ [v])[
            (BFSParentPath.vertices hprev).length] = v := by
          simpa using List.getElem_append_right (BFSParentPath.vertices hprev) [v]
            (BFSParentPath.vertices hprev).length le_rfl (by simp)
        rcases hinv.parent_step u v hpar with ⟨_, d, hdu, hdv⟩
        have hlv : state.level v = state.level u + 1 := by
          simp [BFSState.level, hdu, hdv]
        have hlen := BFSParentPath.vertices_length (h := hprev)
        have hne : BFSParentPath.vertices hprev ≠ [] := by
          rw [← List.length_pos_iff, hlen]
          omega
        have hlast := hprev.vertices_getLast
        have hgetlast : (BFSParentPath.vertices hprev)[
            (BFSParentPath.vertices hprev).length - 1] = u := by
          rw [← List.getLast_eq_getElem hne]
          exact List.getLast_of_getLast?_eq_some hlast
        have hih := ih ((BFSParentPath.vertices hprev).length - 1) (by
          rw [hlen]
          omega)
        have hlu : state.level u = n := by
          rw [hgetlast] at hih
          have : (BFSParentPath.vertices hprev).length - 1 = n := by omega
          simpa [this] using hih
        simp [BFSParentPath.vertices]
        rw [hlv, hlu]
        rw [BFSParentPath.vertices_length (h := hprev)]

/-- The parent path is a simple list: BFS levels strictly increase along it. -/
lemma BFSParentPath.vertices_nodup {φ : Flow V G} {s : V} {state : BFSState V}
    (hinv : BFSDistanceInvariant φ s state) {v : V} {n : ℕ}
    (h : BFSParentPath state.parent s v n) : (BFSParentPath.vertices h).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  apply Fin.ext
  have hli := h.vertices_level_getElem hinv i.1 i.2
  have hlj := h.vertices_level_getElem hinv j.1 j.2
  have hcong := congrArg (state.level) hij
  calc
    i.1 = state.level (h.vertices[i.1]) := hli.symm
    _ = state.level (h.vertices[j.1]) := hcong
    _ = j.1 := hlj

/-- The parent chain from the sink assembles a simple residual path whose
edge count realizes the recorded distance. -/
noncomputable def bfsParentResidualPath (φ : Flow V G) {d : ℕ}
    (hd : (residualBFS φ).distance G.t = some d) : Flow.ResidualPath φ G.s G.t := by
  let hpp := (residualBFS_distanceInvariant φ).parentPath_of_distance hd
  exact { vertices := BFSParentPath.vertices hpp
        , chain := hpp.vertices_chain (residualBFS_distanceInvariant φ)
        , head_eq := hpp.vertices_head
        , last_eq := hpp.vertices_getLast
        , nodup := hpp.vertices_nodup (residualBFS_distanceInvariant φ) }

/-- The parent-chain path realizes the recorded distance. -/
lemma bfsParentResidualPath_edges_length (φ : Flow V G) {d : ℕ}
    (hd : (residualBFS φ).distance G.t = some d) :
    (bfsParentResidualPath φ hd).edges.length = d := by
  rw [Flow.ResidualPath.edges_length]
  simp [bfsParentResidualPath, BFSParentPath.vertices_length]

/-- **Executable shortest augmenting path.**  When the sink is residual
reachable, the BFS parent chain from the sink is a shortest augmenting path. -/
noncomputable def bfs_shortestAugmenting (φ : Flow V G) (h : φ.hasAugmentingPath) :
    ShortestAugmentingPath φ := by
  have hd' : ∃ d, (residualBFS φ).distance G.t = some d :=
    (bfsState_distance_defined_iff_reachable φ G.t).2 h
  let d := Classical.choose hd'
  have hd : (residualBFS φ).distance G.t = some d := Classical.choose_spec hd'
  have hshort : IsShortestDist φ G.s G.t d :=
    (bfsState_distance_eq_some_iff φ G.t).1 hd
  let p : Flow.AugmentingPath φ := bfsParentResidualPath φ hd
  have hlen : p.edges.length = d := by
    simpa [p] using bfsParentResidualPath_edges_length φ hd
  exact { path := p, h_shortest := by simpa [hlen] using hshort }

/-- **BFS drives the Edmonds-Karp step.**  `ekStep` augments along a shortest
path whose length is the one the executable BFS computes: both realize the
same residual distance. -/
theorem ekStep_shortest_path_bfs (φ : Flow V G) (h : φ.hasAugmentingPath) :
    ∃ p : ShortestAugmentingPath φ, ekStep φ = φ.augment p.path ∧
      p.path.edges.length = (bfs_shortestAugmenting φ h).path.edges.length := by
  have hnon : Nonempty (ShortestAugmentingPath φ) :=
    (shortestAugmentingPath_iff_hasAugmentingPath φ).mpr h
  refine ⟨Classical.choice hnon, ?_, ?_⟩
  · unfold ekStep
    simp [hnon]
  · exact (Classical.choice hnon).h_shortest.unique (bfs_shortestAugmenting φ h).h_shortest

end Chapter26
end CLRS
