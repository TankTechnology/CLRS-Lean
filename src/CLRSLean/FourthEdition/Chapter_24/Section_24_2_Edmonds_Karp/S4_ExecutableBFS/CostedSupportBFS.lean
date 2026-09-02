import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.SupportAdjacency

/-!
# Costed residual BFS over finite support buckets

This is the adjacency-list execution companion to `residualBFS`.  A step
reads only the bucket of the dequeued vertex and charges one dequeue plus four
RAM operations per inspected candidate (residual test, visited test, and the
possible discovery bookkeeping).  Under residual-support coverage, erasing
the counter gives the existing semantic BFS state exactly.

As in the textbook RAM model, bucket access and queue/discovery primitives
carry stipulated unit charges.  The attached counter measures that abstract
execution, not Lean evaluator time for the underlying persistent containers.
-/

namespace CLRS
namespace Chapter26

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- A support contains every residual edge of `φ`. -/
def SupportsResidual (A : SupportAdjacency V) (φ : Flow V G) : Prop :=
  ∀ ⦃u v⦄, Flow.residualEdge φ u v → v ∈ A.bucket u

/-- Residual candidates in the bucket of `u`. -/
noncomputable def supportResidualAdj (A : SupportAdjacency V)
    (φ : Flow V G) (u : V) : Finset V :=
  (A.bucket u).filter fun v => Flow.residualEdge φ u v

/-- Undiscovered residual candidates in the bucket of `u`. -/
noncomputable def supportBFSNewNeighbors (A : SupportAdjacency V)
    (φ : Flow V G) (state : BFSState V) (u : V) : Finset V :=
  (supportResidualAdj A φ u).filter fun v => v ∉ state.visited

/-- The ordinary BFS state update, using only a support bucket. -/
noncomputable def supportBFSStateAdvance (A : SupportAdjacency V)
    (φ : Flow V G) (state : BFSState V) (u : V) (rest : List V) : BFSState V :=
  let newNeighbors := supportBFSNewNeighbors A φ state u
  let nextDistance := state.level u + 1
  {
    visited := state.visited ∪ newNeighbors
    queue := rest ++ newNeighbors.toList
    distance := fun v =>
      if v ∈ newNeighbors then some nextDistance else state.distance v
    parent := fun v =>
      if v ∈ newNeighbors then some u else state.parent v
  }

theorem supportResidualAdj_eq_residualAdj (A : SupportAdjacency V)
    (φ : Flow V G) (cover : SupportsResidual A φ) (u : V) :
    supportResidualAdj A φ u = residualAdj φ u := by
  ext v
  simp only [supportResidualAdj, Finset.mem_filter, mem_residualAdj]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨cover h, h⟩

theorem supportBFSNewNeighbors_eq_bfsNewNeighbors (A : SupportAdjacency V)
    (φ : Flow V G) (cover : SupportsResidual A φ) (state : BFSState V) (u : V) :
    supportBFSNewNeighbors A φ state u = bfsNewNeighbors φ state u := by
  simp [supportBFSNewNeighbors, bfsNewNeighbors,
    supportResidualAdj_eq_residualAdj A φ cover u]

theorem supportBFSStateAdvance_eq_bfsStateAdvance (A : SupportAdjacency V)
    (φ : Flow V G) (cover : SupportsResidual A φ) (state : BFSState V)
    (u : V) (rest : List V) :
    supportBFSStateAdvance A φ state u rest = bfsStateAdvance φ state u rest := by
  simp [supportBFSStateAdvance, bfsStateAdvance,
    supportBFSNewNeighbors_eq_bfsNewNeighbors A φ cover state u]

/-- Result of the support-bucket execution. -/
structure CostedBFSRun (V : Type*) [DecidableEq V] where
  state : BFSState V
  work : Nat

/-- Work already performed before `state`: every dequeued vertex costs one
unit and four units per candidate in its support bucket. -/
noncomputable def supportBFSWork (A : SupportAdjacency V)
    (visited : Finset V) (queue : List V) : Nat :=
  let processed := visited \ queue.toFinset
  processed.card + 4 * ∑ u ∈ processed, (A.bucket u).card

theorem mem_supportBFSNewNeighbors_iff {A : SupportAdjacency V}
    {φ : Flow V G} {state : BFSState V} {u v : V} :
    v ∈ supportBFSNewNeighbors A φ state u ↔
      v ∈ A.bucket u ∧ Flow.residualEdge φ u v ∧ v ∉ state.visited := by
  simp [supportBFSNewNeighbors, supportResidualAdj, and_assoc]

/-- Dequeuing `u` advances the work measure by the exact charge recorded by
the recursive execution. -/
theorem supportBFSWork_step (A : SupportAdjacency V) (φ : Flow V G)
    {u : V} {rest : List V} {state : BFSState V}
    (hu : u ∈ state.visited) (hu_rest : u ∉ rest) :
    supportBFSWork A (supportBFSStateAdvance A φ state u rest).visited
        (supportBFSStateAdvance A φ state u rest).queue =
      supportBFSWork A state.visited (u :: rest) + 1 + 4 * (A.bucket u).card := by
  let newNeighbors := supportBFSNewNeighbors A φ state u
  have hnotVisited {x : V} (hx : x ∈ newNeighbors) : x ∉ state.visited :=
    (mem_supportBFSNewNeighbors_iff.mp hx).2.2
  have huNew : u ∉ newNeighbors := by
    intro h
    exact hnotVisited h hu
  have hdequeued :
      (state.visited ∪ newNeighbors) \ (rest.toFinset ∪ newNeighbors) =
        insert u (state.visited \ insert u rest.toFinset) := by
    ext x
    by_cases hxNew : x ∈ newNeighbors
    · simp [hxNew, hnotVisited hxNew]
      intro hxu
      rw [hxu] at hxNew
      exact huNew hxNew
    · simp [hxNew]
      constructor
      · rintro ⟨hxVisited, hxRest⟩
        by_cases hxu : x = u
        · exact Or.inl hxu
        · exact Or.inr ⟨hxVisited, hxu, hxRest⟩
      · rintro (hxu | ⟨hxVisited, _hxne, hxRest⟩)
        · subst x
          exact ⟨hu, hu_rest⟩
        · exact ⟨hxVisited, hxRest⟩
  simp [supportBFSWork, supportBFSStateAdvance]
  rw [hdequeued]
  have huProcessed : u ∉ state.visited \ insert u rest.toFinset := by simp
  simp [huProcessed]
  omega

/-- A support-BFS step preserves duplicate-freedom of the queue. -/
theorem supportBFSStateAdvance_queue_nodup (A : SupportAdjacency V)
    (φ : Flow V G) {state : BFSState V} {u : V} {rest : List V}
    (hnodup : (u :: rest).Nodup)
    (hqueue : BFSQueueInv φ state.visited (u :: rest)) :
    (supportBFSStateAdvance A φ state u rest).queue.Nodup := by
  let newNeighbors := supportBFSNewNeighbors A φ state u
  have hrest : rest.Nodup := (List.nodup_cons.mp hnodup).2
  have hnew : newNeighbors.toList.Nodup := Finset.nodup_toList newNeighbors
  have hdisjoint : ∀ a ∈ rest, ∀ b ∈ newNeighbors.toList, a ≠ b := by
    intro a ha b hb hab
    rw [← hab] at hb
    have haVisited : a ∈ state.visited := hqueue a (by simp [ha])
    have haNew : a ∈ newNeighbors := Finset.mem_toList.mp hb
    exact (mem_supportBFSNewNeighbors_iff.mp haNew).2.2 haVisited
  have : (rest ++ newNeighbors.toList).Nodup := by
    rw [List.nodup_append]
    exact ⟨hrest, hnew, hdisjoint⟩
  simpa [supportBFSStateAdvance, newNeighbors] using this

/-- Fuelled costed support BFS. -/
noncomputable def costedBFSAux (A : SupportAdjacency V) (φ : Flow V G) :
    Nat → BFSState V → CostedBFSRun V
  | 0, state => ⟨state, 0⟩
  | fuel + 1, state =>
      match state.queue with
      | [] => ⟨state, 0⟩
      | u :: rest =>
          let tail := costedBFSAux A φ fuel
            (supportBFSStateAdvance A φ state u rest)
          ⟨tail.state, 1 + 4 * (A.bucket u).card + tail.work⟩

/-- Costed support BFS, fuelled by the finite vertex count. -/
noncomputable def costedResidualBFS (A : SupportAdjacency V)
    (φ : Flow V G) : CostedBFSRun V :=
  costedBFSAux A φ (Fintype.card V) (bfsStateInit G.s)

theorem costedBFSAux_state (A : SupportAdjacency V) (φ : Flow V G)
    (cover : SupportsResidual A φ) (fuel : Nat) (state : BFSState V) :
    (costedBFSAux A φ fuel state).state = bfsStateAux φ fuel state := by
  induction fuel generalizing state with
  | zero => simp [costedBFSAux, bfsStateAux]
  | succ fuel ih =>
      cases hqueue : state.queue with
      | nil => simp [costedBFSAux, bfsStateAux, hqueue]
      | cons u rest =>
          simp only [costedBFSAux, bfsStateAux, hqueue]
          rw [ih]
          exact congrArg (bfsStateAux φ fuel)
            (supportBFSStateAdvance_eq_bfsStateAdvance A φ cover state u rest)

/-- Erasing the support execution and counters gives the existing residual
BFS state exactly. -/
theorem costedResidualBFS_state (A : SupportAdjacency V) (φ : Flow V G)
    (cover : SupportsResidual A φ) :
    (costedResidualBFS A φ).state = residualBFS φ := by
  exact costedBFSAux_state A φ cover (Fintype.card V) (bfsStateInit G.s)

/-- The accumulated recursive counter equals the increase of the execution
work measure. -/
theorem costedBFSAux_work_eq (A : SupportAdjacency V) (φ : Flow V G)
    (cover : SupportsResidual A φ) (fuel : Nat) (state : BFSState V)
    (hqueue : BFSQueueInv φ state.visited state.queue)
    (hnodup : state.queue.Nodup) :
    (costedBFSAux A φ fuel state).work +
        supportBFSWork A state.visited state.queue =
      supportBFSWork A (costedBFSAux A φ fuel state).state.visited
        (costedBFSAux A φ fuel state).state.queue := by
  induction fuel generalizing state with
  | zero => simp [costedBFSAux]
  | succ fuel ih =>
      cases hq : state.queue with
      | nil => simp [costedBFSAux, hq]
      | cons u rest =>
          have hqueueCons : BFSQueueInv φ state.visited (u :: rest) := by
            simpa [hq] using hqueue
          have hnodupCons : (u :: rest).Nodup := by simpa [hq] using hnodup
          let next := supportBFSStateAdvance A φ state u rest
          have hnextEq : next = bfsStateAdvance φ state u rest :=
            supportBFSStateAdvance_eq_bfsStateAdvance A φ cover state u rest
          have hqueueNext : BFSQueueInv φ next.visited next.queue := by
            rw [hnextEq]
            exact bfsQueueInv_step hqueueCons
          have hnodupNext : next.queue.Nodup := by
            exact supportBFSStateAdvance_queue_nodup A φ hnodupCons hqueueCons
          have hih := ih next hqueueNext hnodupNext
          have hu : u ∈ state.visited := hqueue u (by simp [hq])
          have huRest : u ∉ rest := (List.nodup_cons.mp hnodupCons).1
          have hstep := supportBFSWork_step A φ hu huRest
          simp only [costedBFSAux, hq]
          change 1 + 4 * (A.bucket u).card +
              (costedBFSAux A φ fuel next).work +
                supportBFSWork A state.visited (u :: rest) =
            supportBFSWork A (costedBFSAux A φ fuel next).state.visited
              (costedBFSAux A φ fuel next).state.queue
          rw [← hih, hstep]
          omega

theorem supportBFSWork_init (A : SupportAdjacency V) (s : V) :
    supportBFSWork A (bfsStateInit s).visited (bfsStateInit s).queue = 0 := by
  simp [supportBFSWork, bfsStateInit]

/-- The actual support-BFS scan execution is linear in vertices plus stored
candidate arcs. -/
theorem costedResidualBFS_scanWork_le (A : SupportAdjacency V) (φ : Flow V G)
    (cover : SupportsResidual A φ) :
    (costedResidualBFS A φ).work ≤ Fintype.card V + 4 * A.storage := by
  have hinitQueue : BFSQueueInv φ (bfsStateInit G.s).visited
      (bfsStateInit G.s).queue := by
    intro v hv
    simpa [BFSQueueInv, bfsStateInit] using hv
  have hinitNodup : (bfsStateInit G.s).queue.Nodup := by
    simp [bfsStateInit]
  have hcost := costedBFSAux_work_eq A φ cover (Fintype.card V)
    (bfsStateInit G.s) hinitQueue hinitNodup
  have hzero := supportBFSWork_init A G.s
  have hqueueEmpty : (costedResidualBFS A φ).state.queue = [] := by
    rw [costedResidualBFS_state A φ cover]
    exact residualBFS_queue_empty φ
  have hcostEq : (costedResidualBFS A φ).work =
      supportBFSWork A (costedResidualBFS A φ).state.visited
        (costedResidualBFS A φ).state.queue := by
    rw [hzero] at hcost
    simpa [costedResidualBFS] using hcost
  rw [hcostEq, hqueueEmpty]
  simp only [supportBFSWork, List.toFinset_nil, Finset.sdiff_empty]
  have hcard : (costedResidualBFS A φ).state.visited.card ≤ Fintype.card V :=
    Finset.card_le_univ _
  have hsum :
      ∑ u ∈ (costedResidualBFS A φ).state.visited, (A.bucket u).card ≤ A.storage :=
    sum_bucket_card_le_storage A _
  omega

/-- Public work bound for the costed support BFS. -/
theorem costedResidualBFS_work_le (A : SupportAdjacency V) (φ : Flow V G)
    (cover : SupportsResidual A φ) :
    (costedResidualBFS A φ).work ≤ Fintype.card V + 4 * A.storage :=
  costedResidualBFS_scanWork_le A φ cover

/-! ## Attached parent-path recovery -/

/-- A recovered path list and the work performed to construct it. -/
structure CostedPathVertices (V : Type*) where
  vertices : List V
  work : Nat

namespace BFSParentPath

/-- Build the parent path in reverse order using constant-time list cons. -/
noncomputable def reverseVerticesWithCost {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) : CostedPathVertices V :=
  match h with
  | root => ⟨[s], 1⟩
  | @tail _ _ _ _ v _ hprev _ =>
      let prev := reverseVerticesWithCost hprev
      ⟨v :: prev.vertices, prev.work + 1⟩

omit [Fintype V] [DecidableEq V] in
theorem reverseVerticesWithCost_vertices {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) :
    (reverseVerticesWithCost h).vertices = (BFSParentPath.vertices h).reverse := by
  induction h with
  | root => rfl
  | @tail u v n hprev hparent ih =>
      simp [reverseVerticesWithCost, BFSParentPath.vertices, ih]

omit [Fintype V] [DecidableEq V] in
theorem reverseVerticesWithCost_work {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) :
    (reverseVerticesWithCost h).work = n + 1 := by
  induction h with
  | root => rfl
  | @tail u v n hprev hparent ih =>
      simp [reverseVerticesWithCost, ih]

/-- Recover source-to-target order and charge the final linear reversal. -/
noncomputable def verticesWithCost {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) : CostedPathVertices V :=
  let reverseRun := reverseVerticesWithCost h
  ⟨reverseRun.vertices.reverse, reverseRun.work + reverseRun.vertices.length⟩

omit [Fintype V] [DecidableEq V] in
theorem verticesWithCost_vertices {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) :
    (verticesWithCost h).vertices = BFSParentPath.vertices h := by
  simp [verticesWithCost, reverseVerticesWithCost_vertices]

theorem verticesWithCost_work {parent : V → Option V} {s v : V} {n : Nat}
    (h : BFSParentPath parent s v n) :
    (verticesWithCost h).work = 2 * (n + 1) := by
  simp [verticesWithCost, reverseVerticesWithCost_work,
    reverseVerticesWithCost_vertices, BFSParentPath.vertices_length]
  omega

end BFSParentPath

end Chapter26
end CLRS
