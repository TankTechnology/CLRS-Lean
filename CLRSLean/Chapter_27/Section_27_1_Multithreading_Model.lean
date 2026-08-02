import Mathlib.Tactic

/-!
# 27.1. The Basics of Dynamic Multithreading

This section formalizes the dynamic-multithreading model of CLRS §27.1.

- **Strand**: an atomic unit of computation with a work weight.
- **Computation DAG** (`CompDAG`): nodes carry strand work; edges `(u, v)`
  record that `u` must complete before `v` starts.  We require edges to point
  from smaller to larger indices (`h_edges_forward`), so the index order is a
  topological order and the graph is acyclic by construction.
- **Work T₁** (`CompDAG.work`): the sum of all node weights.
- **Span T∞** (`CompDAG.span`): the longest weighted path, computed honestly
  by dynamic programming over the topological order (`CompDAG.longestTo`).
- **Spawn tree** (`SpawnTree`): the spawn/sync pattern of a parallel
  divide-and-conquer computation.  A `spawn` node contributes unit work and
  unit span (the spawn/sync overhead), so the critical path of a balanced
  spawn tree is logarithmic, matching the textbook analysis.
- **Parallel loops** (`parallelLoopTree`): a balanced binary spawn tree over
  `n` iterations, with proved work and span characterizations.

Main results:

- `CompDAG.longestTo_le`, `CompDAG.span_le_work`: the span never exceeds the
  work (T∞ ≤ T₁).
- `DAGSchedule.time_le_work_div_add_span`: the CLRS complete-step /
  incomplete-step argument gives `Tₚ ≤ T₁ / p + T∞` for an explicit greedy
  execution of the computation DAG.
- `SpawnTree.span_le_work`: the same inequality for spawn trees.
- `parallelLoop_work`: the work of the parallel-loop tree is exactly
  `n * w + (n - 1)`.
- `parallelLoop_span`: the span is exactly `w + parallelLoopDepth n` for
  `n ≥ 2`, where `parallelLoopDepth` is the balanced halving depth.
- `parallelLoopDepth_pow`: `n ≤ 2 ^ parallelLoopDepth n`, the
  span-is-logarithmic direction.

## Deferred work

* A matching upper bound `parallelLoopDepth n ≤ Nat.log 2 n + 1` (i.e.
  `Nat.clog`-style exact characterization) is future work.
-/

namespace CLRS
namespace Chapter27

/-! ## Strands and computation DAGs -/

/-- A strand is an atomic unit of computation with a nonnegative work weight:
the number of time units it takes on a single processor. -/
structure Strand where
  /-- Work weight in time units. -/
  work : ℕ
deriving Repr, DecidableEq

/-- A computation DAG models a multithreaded computation.

Nodes are `0, …, n - 1`, each carrying a strand weight.  An edge `(u, v)`
means `u` must complete before `v` can begin.  Edges are required to point
forward (`u < v`), so the node order is a topological order. -/
structure CompDAG where
  /-- Number of nodes in the DAG. -/
  n : ℕ
  /-- Work weight for each node. -/
  node_work : ℕ → ℕ
  /-- Dependency edges. -/
  edges : List (ℕ × ℕ)
  /-- All edges reference valid, distinct nodes. -/
  h_edges_in_bounds : ∀ uv ∈ edges, uv.1 < n ∧ uv.2 < n ∧ uv.1 ≠ uv.2 := by
    simp
  /-- Edges point forward, so the graph is acyclic and topologically ordered. -/
  h_edges_forward : ∀ uv ∈ edges, uv.1 < uv.2

namespace CompDAG

/-- The total work T₁: the sum of the work over all nodes. -/
def work (G : CompDAG) : ℕ :=
  ∑ i ∈ Finset.range G.n, G.node_work i

/-- The longest weighted path ending at node `v`: `v`'s own weight plus the
maximum over the longest paths ending at its immediate predecessors
(`0` when `v` has no predecessors). -/
def longestTo (G : CompDAG) (v : ℕ) : ℕ :=
  G.node_work v +
    ((G.edges.filter fun e => e.2 = v).attach.map fun e =>
      G.longestTo e.1.1).foldr max 0
termination_by v
decreasing_by
  have hfilt := List.mem_filter.mp e.2
  have hfwd := G.h_edges_forward e.1 hfilt.1
  have hveq : e.1.2 = v := of_decide_eq_true hfilt.2
  omega

/-- The span T∞: the maximum of `longestTo` over all nodes — the critical
path length, a lower bound on the parallel running time. -/
def span (G : CompDAG) : ℕ :=
  ((List.range G.n).map G.longestTo).foldr max 0

/-- The speedup on `p` processors with observed time `Tp`: T₁ / Tp. -/
def speedup (G : CompDAG) (Tp : ℕ) : ℚ :=
  if Tp = 0 then 0 else (G.work : ℚ) / (Tp : ℚ)

/-- The parallelism of the computation: T₁ / T∞. -/
noncomputable def parallelism (G : CompDAG) : ℚ :=
  if G.span = 0 then 0 else (G.work : ℚ) / (G.span : ℚ)

private theorem foldr_max_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) :
    l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le B
  | cons x xs ih =>
      simp only [List.foldr_cons]
      have hx := h x List.mem_cons_self
      have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      omega

/-- The longest path ending at `v` uses only nodes `≤ v`, so its weight is
bounded by the partial work sum. -/
theorem longestTo_le (G : CompDAG) (v : ℕ) :
    G.longestTo v ≤ ∑ i ∈ Finset.range (v + 1), G.node_work i := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      rw [Finset.sum_range_succ, longestTo]
      have hfold :
          ((G.edges.filter fun e => e.2 = v).attach.map fun e =>
              G.longestTo e.1.1).foldr max 0 ≤
            ∑ i ∈ Finset.range v, G.node_work i := by
        apply foldr_max_le
        intro x hx
        rcases List.mem_map.mp hx with ⟨⟨e, he⟩, -, rfl⟩
        have hfilt := List.mem_filter.mp he
        have hfwd := G.h_edges_forward e hfilt.1
        have hveq : e.2 = v := of_decide_eq_true hfilt.2
        have hlt : e.1 < v := by rw [← hveq]; exact hfwd
        calc G.longestTo e.1
            ≤ ∑ i ∈ Finset.range (e.1 + 1), G.node_work i := ih e.1 hlt
          _ ≤ ∑ i ∈ Finset.range v, G.node_work i :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_iff.mpr fun x hx =>
                Finset.mem_range.mpr (by
                  have hx' := Finset.mem_range.mp hx
                  omega))
              (by simp)
      omega

/-- T∞ ≤ T₁: the span never exceeds the total work. -/
theorem span_le_work (G : CompDAG) : G.span ≤ G.work := by
  unfold span work
  apply foldr_max_le
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  have hi' : i < G.n := List.mem_range.mp hi
  calc G.longestTo i
      ≤ ∑ j ∈ Finset.range (i + 1), G.node_work j := G.longestTo_le i
    _ ≤ ∑ j ∈ Finset.range G.n, G.node_work j :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_iff.mpr fun x hx =>
          Finset.mem_range.mpr (by
            have hx' := Finset.mem_range.mp hx
            omega))
              (by simp)

/-! ### Residual computation states -/

/-- Work remaining in a partially executed computation. -/
def remainingWork (G : CompDAG) (remaining : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range G.n, remaining i

/-- Reuse the dependency graph with a new node-work function. -/
def withWork (G : CompDAG) (nodeWork : ℕ → ℕ) : CompDAG where
  n := G.n
  node_work := nodeWork
  edges := G.edges
  h_edges_in_bounds := G.h_edges_in_bounds
  h_edges_forward := G.h_edges_forward

/-- Critical-path work remaining in a partially executed computation. -/
def remainingSpan (G : CompDAG) (remaining : ℕ → ℕ) : ℕ :=
  (G.withWork remaining).span

/-- Execute one unit of work at each selected node. -/
def execute (_G : CompDAG) (remaining : ℕ → ℕ) (run : Finset ℕ) : ℕ → ℕ :=
  fun v => if v ∈ run then remaining v - 1 else remaining v

private theorem foldr_max_map_le {α : Type} (items : List α) (f g : α → ℕ)
    (hfg : ∀ item ∈ items, f item ≤ g item) :
    (items.map f).foldr max 0 ≤ (items.map g).foldr max 0 := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le_max (hfg item List.mem_cons_self)
        (ih fun tailItem hmem => hfg tailItem (List.mem_cons_of_mem item hmem))

private theorem foldr_max_map_add_one_le {α : Type} (items : List α)
    (f : α → ℕ) (bound : ℕ) (hbound : 0 < bound)
    (hf : ∀ item ∈ items, f item + 1 ≤ bound) :
    (items.map f).foldr max 0 + 1 ≤ bound := by
  induction items with
  | nil => simp; omega
  | cons item items ih =>
      have hitem := hf item List.mem_cons_self
      have htail := ih fun tailItem hmem =>
        hf tailItem (List.mem_cons_of_mem item hmem)
      simp only [List.map_cons, List.foldr_cons]
      rcases le_total (f item) ((items.map f).foldr max 0) with hle | hge
      · rw [max_eq_right hle]
        exact htail
      · rw [max_eq_left hge]
        exact hitem

/-- Increasing node work can only increase the longest path ending at a node. -/
theorem longestTo_mono_work (G : CompDAG) (smaller larger : ℕ → ℕ)
    (hwork : ∀ v, smaller v ≤ larger v) (v : ℕ) :
    (G.withWork smaller).longestTo v ≤ (G.withWork larger).longestTo v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      rw [longestTo, longestTo]
      apply Nat.add_le_add (hwork v)
      apply foldr_max_map_le
      intro edge _hmem
      have hfilt := List.mem_filter.mp edge.property
      have htarget : edge.val.2 = v := of_decide_eq_true hfilt.2
      have hsource_lt : edge.val.1 < v := by
        have hforward := G.h_edges_forward edge.val hfilt.1
        omega
      exact ih edge.val.1 hsource_lt

/-- Residual span is monotone in every node's remaining work. -/
theorem remainingSpan_mono (G : CompDAG) (smaller larger : ℕ → ℕ)
    (hwork : ∀ v, smaller v ≤ larger v) :
    G.remainingSpan smaller ≤ G.remainingSpan larger := by
  unfold remainingSpan span
  apply foldr_max_map_le
  intro v _hv
  exact G.longestTo_mono_work smaller larger hwork v

/-- Executing work cannot increase the residual critical path. -/
theorem remainingSpan_execute_le (G : CompDAG) (remaining : ℕ → ℕ)
    (run : Finset ℕ) :
    G.remainingSpan (G.execute remaining run) ≤ G.remainingSpan remaining := by
  apply G.remainingSpan_mono
  intro v
  simp only [execute]
  split <;> omega

/-- Nodes that have positive remaining work and whose immediate predecessors
have finished. -/
def ready (G : CompDAG) (remaining : ℕ → ℕ) : Finset ℕ :=
  (Finset.range G.n).filter fun v =>
    0 < remaining v ∧
      ∀ edge ∈ G.edges, edge.2 = v → remaining edge.1 = 0

theorem mem_ready_iff (G : CompDAG) (remaining : ℕ → ℕ) (v : ℕ) :
    v ∈ G.ready remaining ↔
      v < G.n ∧ 0 < remaining v ∧
        ∀ edge ∈ G.edges, edge.2 = v → remaining edge.1 = 0 := by
  simp [ready]

private theorem longestTo_execute_ready_add_one_le (G : CompDAG)
    (remaining : ℕ → ℕ) (v : ℕ) (hv : v < G.n)
    (hpositive : 0 < (G.withWork remaining).longestTo v) :
    (G.withWork (G.execute remaining (G.ready remaining))).longestTo v + 1 ≤
      (G.withWork remaining).longestTo v := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
      let predEdges := (G.edges.filter fun edge => edge.2 = v).attach
      let beforeMax :=
        (predEdges.map fun edge =>
          (G.withWork remaining).longestTo edge.val.1).foldr max 0
      let afterMax :=
        (predEdges.map fun edge =>
          (G.withWork (G.execute remaining (G.ready remaining))).longestTo
            edge.val.1).foldr max 0
      rw [longestTo] at hpositive
      rw [longestTo, longestTo]
      change 0 < remaining v + beforeMax at hpositive
      change G.execute remaining (G.ready remaining) v + afterMax + 1 ≤
        remaining v + beforeMax
      have hnode_mono : ∀ node,
          G.execute remaining (G.ready remaining) node ≤ remaining node := by
        intro node
        simp only [execute]
        split <;> omega
      have hmax_mono : afterMax ≤ beforeMax := by
        apply foldr_max_map_le
        intro edge _hmem
        exact G.longestTo_mono_work _ _ hnode_mono edge.val.1
      have hmax_drop (hmax_positive : 0 < beforeMax) :
          afterMax + 1 ≤ beforeMax := by
        apply foldr_max_map_add_one_le predEdges _ beforeMax hmax_positive
        intro edge _hmem
        have hfilt := List.mem_filter.mp edge.property
        have htarget : edge.val.2 = v := of_decide_eq_true hfilt.2
        have hsource_lt : edge.val.1 < v := by
          have hforward := G.h_edges_forward edge.val hfilt.1
          omega
        have hsource_bound : edge.val.1 < G.n :=
          (G.h_edges_in_bounds edge.val hfilt.1).1
        by_cases hpred_positive :
            0 < (G.withWork remaining).longestTo edge.val.1
        · have hdrop := ih edge.val.1 hsource_lt hsource_bound hpred_positive
          have hmem : (G.withWork remaining).longestTo edge.val.1 ∈
              predEdges.map fun predecessor =>
                (G.withWork remaining).longestTo predecessor.val.1 :=
            List.mem_map.mpr ⟨edge, _hmem, rfl⟩
          have hle := List.le_max_of_le' 0 hmem (le_refl _)
          exact hdrop.trans hle
        · have hbefore_zero :
              (G.withWork remaining).longestTo edge.val.1 = 0 :=
            Nat.eq_zero_of_not_pos hpred_positive
          have hafter_le :=
            G.longestTo_mono_work _ _ hnode_mono edge.val.1
          have hafter_zero :
              (G.withWork (G.execute remaining (G.ready remaining))).longestTo
                  edge.val.1 = 0 := by
            omega
          omega
      by_cases hready : v ∈ G.ready remaining
      · have hvpos := ((G.mem_ready_iff remaining v).mp hready).2.1
        have hexecute :
            G.execute remaining (G.ready remaining) v = remaining v - 1 := by
          simp [execute, hready]
        rw [hexecute]
        omega
      · have hbefore_max_positive : 0 < beforeMax := by
          by_cases hvpos : 0 < remaining v
          · have hnot_all :
                ¬ ∀ edge ∈ G.edges,
                  edge.2 = v → remaining edge.1 = 0 := by
              intro hall
              exact hready ((G.mem_ready_iff remaining v).mpr ⟨hv, hvpos, hall⟩)
            push Not at hnot_all
            obtain ⟨edge, hedge, htarget, hsource_ne⟩ := hnot_all
            let attached :
                { candidate // candidate ∈
                  (G.edges.filter fun candidate => candidate.2 = v) } :=
              ⟨edge, List.mem_filter.mpr ⟨hedge, by simp [htarget]⟩⟩
            have hsource_pos : 0 < remaining edge.1 := Nat.pos_of_ne_zero hsource_ne
            have hlongest_pos :
                0 < (G.withWork remaining).longestTo edge.1 := by
              rw [longestTo]
              change 0 < remaining edge.1 + _
              omega
            have hmem :
                (G.withWork remaining).longestTo edge.1 ∈
                  predEdges.map fun predecessor =>
                    (G.withWork remaining).longestTo predecessor.val.1 :=
              List.mem_map.mpr ⟨attached, by
                simp [predEdges], rfl⟩
            have hle := List.le_max_of_le' 0 hmem (le_refl _)
            exact Nat.lt_of_lt_of_le hlongest_pos hle
          · have hvzero : remaining v = 0 := Nat.eq_zero_of_not_pos hvpos
            omega
        have hexecute :
            G.execute remaining (G.ready remaining) v = remaining v := by
          simp [execute, hready]
        rw [hexecute]
        exact Nat.add_le_add_left (hmax_drop hbefore_max_positive) (remaining v)

/-- If unfinished work remains, executing every ready node removes at least one
unit from the residual critical path. -/
theorem remainingSpan_execute_ready_add_one_le (G : CompDAG)
    (remaining : ℕ → ℕ) (hwork : 0 < G.remainingWork remaining) :
    G.remainingSpan (G.execute remaining (G.ready remaining)) + 1 ≤
      G.remainingSpan remaining := by
  have hwork' : 0 < ∑ v ∈ Finset.range G.n, remaining v := by
    simpa [remainingWork] using hwork
  obtain ⟨v, hvrange, hvpos⟩ := Finset.sum_pos_iff.mp hwork'
  have hvlt : v < G.n := Finset.mem_range.mp hvrange
  have hlongest_pos : 0 < (G.withWork remaining).longestTo v := by
    rw [longestTo]
    change 0 < remaining v + _
    omega
  have hspan_positive : 0 < G.remainingSpan remaining := by
    unfold remainingSpan span
    have hmem : (G.withWork remaining).longestTo v ∈
        (List.range G.n).map (G.withWork remaining).longestTo :=
      List.mem_map.mpr ⟨v, List.mem_range.mpr hvlt, rfl⟩
    have hle := List.le_max_of_le' 0 hmem (le_refl _)
    exact Nat.lt_of_lt_of_le hlongest_pos hle
  unfold remainingSpan span
  apply foldr_max_map_add_one_le (List.range G.n) _ _ hspan_positive
  intro node hnode
  have hnode_lt : node < G.n := List.mem_range.mp hnode
  by_cases hnode_positive : 0 < (G.withWork remaining).longestTo node
  · have hdrop :=
      G.longestTo_execute_ready_add_one_le remaining node hnode_lt hnode_positive
    have hmem : (G.withWork remaining).longestTo node ∈
        (List.range G.n).map (G.withWork remaining).longestTo :=
      List.mem_map.mpr ⟨node, hnode, rfl⟩
    have hle := List.le_max_of_le' 0 hmem (le_refl _)
    exact hdrop.trans hle
  · have hbefore_zero : (G.withWork remaining).longestTo node = 0 :=
      Nat.eq_zero_of_not_pos hnode_positive
    have hnode_mono : ∀ i,
        G.execute remaining (G.ready remaining) i ≤ remaining i := by
      intro i
      simp only [execute]
      split <;> omega
    have hafter_le := G.longestTo_mono_work _ _ hnode_mono node
    omega

/-- Executing a set of ready nodes consumes exactly one work unit per selected
node. -/
theorem remainingWork_execute_add_card (G : CompDAG) (remaining : ℕ → ℕ)
    (run : Finset ℕ) (hrun : run ⊆ G.ready remaining) :
    G.remainingWork (G.execute remaining run) + run.card =
      G.remainingWork remaining := by
  have hrun_range : run ⊆ Finset.range G.n := by
    intro v hv
    exact Finset.mem_range.mpr ((G.mem_ready_iff remaining v).mp (hrun hv)).1
  have hfilter :
      (Finset.range G.n).filter (fun v => v ∈ run) = run := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact fun hv => hv.2
    · exact fun hv => ⟨hrun_range hv, hv⟩
  have hcard :
      (∑ v ∈ Finset.range G.n, if v ∈ run then 1 else 0) = run.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  rw [remainingWork, remainingWork, ← hcard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvrun : v ∈ run
  · have hvpos : 0 < remaining v :=
      ((G.mem_ready_iff remaining v).mp (hrun hvrun)).2.1
    simp [execute, hvrun, Nat.sub_add_cancel hvpos]
  · simp [execute, hvrun]

end CompDAG

/-! ## Greedy-scheduler accounting

CLRS partitions a greedy execution into complete steps, which execute one
strand on every processor, and incomplete steps, which execute every ready
strand.  Complete steps are paid for by total work; incomplete steps are paid
for by a unit decrease in the remaining span.  This structure records exactly
the two obligations needed by that argument, independently of the concrete DAG
execution representation that produces them. -/

/-- The accounting certificate extracted from a greedy schedule.

`completeSteps` steps each consume `processors` units of work, while the number
of `incompleteSteps` is bounded by the initial span. -/
structure GreedyScheduleAccounting where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Total work `T₁` of the computation. -/
  totalWork : ℕ
  /-- Initial span `T∞` of the computation. -/
  totalSpan : ℕ
  /-- Number of time steps that use every processor. -/
  completeSteps : ℕ
  /-- Number of time steps that execute fewer than all processors. -/
  incompleteSteps : ℕ
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- Complete steps cannot consume more than the available total work. -/
  complete_work_bound : completeSteps * processors ≤ totalWork
  /-- Every incomplete step consumes at least one unit of remaining span. -/
  incomplete_span_bound : incompleteSteps ≤ totalSpan

namespace GreedyScheduleAccounting

/-- Parallel running time is the number of complete plus incomplete steps. -/
def time (A : GreedyScheduleAccounting) : ℕ :=
  A.completeSteps + A.incompleteSteps

/-- CLRS Theorems 27.1/27.2 at the accounting boundary:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (A : GreedyScheduleAccounting) :
    A.time ≤ A.totalWork / A.processors + A.totalSpan := by
  have hcomplete : A.completeSteps ≤ A.totalWork / A.processors :=
    (Nat.le_div_iff_mul_le A.processors_pos).2 A.complete_work_bound
  exact Nat.add_le_add hcomplete A.incomplete_span_bound

end GreedyScheduleAccounting

/-! ## Greedy-schedule traces -/

/-- Whether a greedy-schedule step keeps every processor busy or exhausts the
currently ready strands before doing so. -/
inductive GreedyStepKind where
  | complete
  | incomplete
deriving Repr, DecidableEq

/-- A finite greedy-schedule trace together with the two global bounds that
justify its complete and incomplete steps.  Unlike
`GreedyScheduleAccounting`, this representation retains the order of steps. -/
structure GreedyScheduleTrace where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Total work `T₁` of the computation. -/
  totalWork : ℕ
  /-- Initial span `T∞` of the computation. -/
  totalSpan : ℕ
  /-- Complete and incomplete steps, in execution order. -/
  steps : List GreedyStepKind
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- The complete steps cannot consume more than the available work. -/
  complete_work_bound : steps.count .complete * processors ≤ totalWork
  /-- The incomplete steps cannot outnumber the initial span. -/
  incomplete_span_bound : steps.count .incomplete ≤ totalSpan

namespace GreedyScheduleTrace

/-- Parallel running time is the number of recorded schedule steps. -/
def time (S : GreedyScheduleTrace) : ℕ :=
  S.steps.length

/-- Forget step order and retain the accounting data used by the bound. -/
def accounting (S : GreedyScheduleTrace) : GreedyScheduleAccounting where
  processors := S.processors
  totalWork := S.totalWork
  totalSpan := S.totalSpan
  completeSteps := S.steps.count .complete
  incompleteSteps := S.steps.count .incomplete
  processors_pos := S.processors_pos
  complete_work_bound := S.complete_work_bound
  incomplete_span_bound := S.incomplete_span_bound

private theorem count_complete_add_count_incomplete
    (steps : List GreedyStepKind) :
    steps.count .complete + steps.count .incomplete = steps.length := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      cases step <;> simp <;> omega

/-- The schedule-trace form of the greedy-scheduler bound:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (S : GreedyScheduleTrace) :
    S.time ≤ S.totalWork / S.processors + S.totalSpan := by
  have h := S.accounting.time_le_work_div_add_span
  rw [GreedyScheduleAccounting.time] at h
  rw [time, ← count_complete_add_count_incomplete S.steps]
  exact h

end GreedyScheduleTrace

/-! ## Per-step greedy-schedule accounting -/

/-- The metric changes caused by one greedy-schedule step. -/
structure GreedyScheduleStep where
  /-- Whether the step filled every processor. -/
  kind : GreedyStepKind
  /-- Amount of remaining work consumed by the step. -/
  workConsumed : ℕ
  /-- Amount by which the remaining span decreases. -/
  spanDecrease : ℕ
deriving Repr, DecidableEq

/-! ## Concrete computation-DAG steps -/

/-- One greedy time step over an explicit residual `CompDAG` state.

`run` contains only ready nodes and has the largest cardinality allowed by the
processor count.  Thus an incomplete step necessarily executes every ready
node. -/
structure DAGScheduleStep (G : CompDAG) (processors : ℕ) where
  /-- Work remaining at every DAG node before the step. -/
  remaining : ℕ → ℕ
  /-- Ready nodes selected for one unit of execution. -/
  run : Finset ℕ
  /-- Only ready nodes may execute. -/
  run_subset_ready : run ⊆ G.ready remaining
  /-- A greedy step uses as many processors as the ready set permits. -/
  run_card_eq_min : run.card = min processors (G.ready remaining).card

namespace DAGScheduleStep

/-- Residual state after executing the selected ready nodes. -/
def after {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : ℕ → ℕ :=
  G.execute S.remaining S.run

/-- A step is complete exactly when it fills every processor. -/
def kind {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : GreedyStepKind :=
  if S.run.card = processors then .complete else .incomplete

/-- Expose a concrete DAG step at the per-step accounting boundary. -/
def metricStep {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) : GreedyScheduleStep where
  kind := S.kind
  workConsumed := S.run.card
  spanDecrease := G.remainingSpan S.remaining - G.remainingSpan S.after

theorem kind_eq_complete_iff {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    S.kind = .complete ↔ S.run.card = processors := by
  simp [kind]

theorem kind_eq_incomplete_iff {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    S.kind = .incomplete ↔ S.run.card ≠ processors := by
  simp [kind]

/-- The concrete residual-work balance for one DAG step. -/
theorem remainingWork_after_add_card {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) :
    G.remainingWork S.after + S.run.card = G.remainingWork S.remaining := by
  exact G.remainingWork_execute_add_card S.remaining S.run S.run_subset_ready

/-- The accounting work obligation is automatic for complete DAG steps. -/
theorem complete_progress {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) (hcomplete : S.kind = .complete) :
    processors ≤ S.metricStep.workConsumed := by
  have hcard := (S.kind_eq_complete_iff).mp hcomplete
  simp [metricStep, hcard]

/-- If a greedy step is incomplete, it executes the entire ready set. -/
theorem incomplete_run_eq_ready {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors) (hincomplete : S.kind = .incomplete) :
    S.run = G.ready S.remaining := by
  have hcard_ne : S.run.card ≠ processors :=
    (S.kind_eq_incomplete_iff).mp hincomplete
  have hready_lt : (G.ready S.remaining).card < processors := by
    by_contra hnot
    have hprocessors_le : processors ≤ (G.ready S.remaining).card :=
      Nat.le_of_not_gt hnot
    have : S.run.card = processors := by
      rw [S.run_card_eq_min, Nat.min_eq_left hprocessors_le]
    exact hcard_ne this
  have hcards : S.run.card = (G.ready S.remaining).card := by
    rw [S.run_card_eq_min, Nat.min_eq_right (Nat.le_of_lt hready_lt)]
  exact Finset.eq_of_subset_of_card_le S.run_subset_ready hcards.ge

/-- The accounting span obligation is automatic for every active incomplete
DAG step. -/
theorem incomplete_progress {G : CompDAG} {processors : ℕ}
    (S : DAGScheduleStep G processors)
    (hactive : 0 < G.remainingWork S.remaining)
    (hincomplete : S.kind = .incomplete) :
    1 ≤ S.metricStep.spanDecrease := by
  have hrun := S.incomplete_run_eq_ready hincomplete
  have hdrop := G.remainingSpan_execute_ready_add_one_le S.remaining hactive
  simp only [metricStep, after]
  rw [hrun]
  omega

end DAGScheduleStep

/-! ## Chained computation-DAG schedules -/

/-- A type-safe sequence of active greedy DAG steps.

The index is the initial residual state.  In the `step` constructor the tail is
indexed by `S.after`, so consecutive states agree by construction. -/
inductive DAGSchedule (G : CompDAG) (processors : ℕ) : (ℕ → ℕ) → Type where
  | done (remaining : ℕ → ℕ) : DAGSchedule G processors remaining
  | step (S : DAGScheduleStep G processors)
      (active : 0 < G.remainingWork S.remaining)
      (tail : DAGSchedule G processors S.after) :
      DAGSchedule G processors S.remaining

namespace DAGSchedule

/-- Per-step accounting records of a chained DAG execution. -/
def metricSteps {G : CompDAG} {processors : ℕ} :
    {remaining : ℕ → ℕ} → DAGSchedule G processors remaining →
      List GreedyScheduleStep
  | _, .done _ => []
  | _, .step S _ tail => S.metricStep :: tail.metricSteps

/-- The residual state where the recorded execution stops. -/
def finalState {G : CompDAG} {processors : ℕ} :
    {remaining : ℕ → ℕ} → DAGSchedule G processors remaining → ℕ → ℕ
  | _, .done remaining => remaining
  | _, .step _ _ tail => tail.finalState

/-- Parallel time of the chained execution. -/
def time {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) : ℕ :=
  D.metricSteps.length

/-- Work consumption telescopes over a chained execution. -/
theorem work_balance {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) :
    (D.metricSteps.map GreedyScheduleStep.workConsumed).sum +
        G.remainingWork D.finalState =
      G.remainingWork remaining := by
  induction D with
  | done => simp [metricSteps, finalState]
  | step S _active tail ih =>
      have hstep := S.remainingWork_after_add_card
      simp only [metricSteps, List.map_cons, List.sum_cons,
        DAGScheduleStep.metricStep]
      change S.run.card +
          (tail.metricSteps.map GreedyScheduleStep.workConsumed).sum +
            G.remainingWork tail.finalState =
        G.remainingWork S.remaining
      omega

/-- Span decreases telescope over a chained execution. -/
theorem span_balance {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) :
    (D.metricSteps.map GreedyScheduleStep.spanDecrease).sum +
        G.remainingSpan D.finalState =
      G.remainingSpan remaining := by
  induction D with
  | done => simp [metricSteps, finalState]
  | step S _active tail ih =>
      have hmono : G.remainingSpan S.after ≤ G.remainingSpan S.remaining := by
        simpa [DAGScheduleStep.after] using
          G.remainingSpan_execute_le S.remaining S.run
      simp only [metricSteps, List.map_cons, List.sum_cons,
        DAGScheduleStep.metricStep, DAGScheduleStep.after]
      change (G.remainingSpan S.remaining - G.remainingSpan S.after) +
          (tail.metricSteps.map GreedyScheduleStep.spanDecrease).sum +
            G.remainingSpan tail.finalState =
        G.remainingSpan S.remaining
      omega

private theorem all_complete_progress {G : CompDAG} {processors : ℕ}
    {remaining : ℕ → ℕ} (D : DAGSchedule G processors remaining) :
    ∀ step ∈ D.metricSteps,
      step.kind = .complete → processors ≤ step.workConsumed := by
  induction D with
  | done => simp [metricSteps]
  | step S _active tail ih =>
      intro step hmem hcomplete
      simp only [metricSteps, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simpa [DAGScheduleStep.metricStep] using S.complete_progress hcomplete
      · exact ih step htail hcomplete

private theorem all_incomplete_progress {G : CompDAG} {processors : ℕ}
    {remaining : ℕ → ℕ} (D : DAGSchedule G processors remaining) :
    ∀ step ∈ D.metricSteps,
      step.kind = .incomplete → 1 ≤ step.spanDecrease := by
  induction D with
  | done => simp [metricSteps]
  | step S active tail ih =>
      intro step hmem hincomplete
      simp only [metricSteps, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simpa [DAGScheduleStep.metricStep] using
          S.incomplete_progress active hincomplete
      · exact ih step htail hincomplete

end DAGSchedule

/-- A schedule run whose resource bounds and progress obligations are stated
locally, one execution step at a time.

The eventual ready-set semantics only needs to produce this interface: a
complete step consumes at least `processors` work, and an incomplete step
decreases the remaining span by at least one. -/
structure GreedyScheduleRun where
  /-- Number of processors used by the schedule. -/
  processors : ℕ
  /-- Initial work `T₁`. -/
  totalWork : ℕ
  /-- Initial span `T∞`. -/
  totalSpan : ℕ
  /-- Metric changes of the execution steps, in order. -/
  steps : List GreedyScheduleStep
  /-- A schedule has at least one processor. -/
  processors_pos : 0 < processors
  /-- All step work consumptions fit within the initial work. -/
  work_budget : (steps.map GreedyScheduleStep.workConsumed).sum ≤ totalWork
  /-- All span decreases fit within the initial span. -/
  span_budget : (steps.map GreedyScheduleStep.spanDecrease).sum ≤ totalSpan
  /-- Every complete step keeps all processors busy. -/
  complete_progress : ∀ step ∈ steps,
    step.kind = .complete → processors ≤ step.workConsumed
  /-- Every incomplete step advances the critical path. -/
  incomplete_progress : ∀ step ∈ steps,
    step.kind = .incomplete → 1 ≤ step.spanDecrease

namespace GreedyScheduleRun

/-- Parallel running time is the number of execution steps. -/
def time (S : GreedyScheduleRun) : ℕ :=
  S.steps.length

private theorem complete_count_mul_le_work
    (processors : ℕ) (steps : List GreedyScheduleStep)
    (hprogress : ∀ step ∈ steps,
      step.kind = .complete → processors ≤ step.workConsumed) :
    (steps.map GreedyScheduleStep.kind).count .complete * processors ≤
      (steps.map GreedyScheduleStep.workConsumed).sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      have htail : ∀ tailStep ∈ steps,
          tailStep.kind = .complete → processors ≤ tailStep.workConsumed := by
        intro tailStep hmem
        exact hprogress tailStep (List.mem_cons_of_mem step hmem)
      have ih' := ih htail
      cases hkind : step.kind with
      | complete =>
          have hstep : processors ≤ step.workConsumed :=
            hprogress step List.mem_cons_self hkind
          simp [hkind]
          rw [Nat.add_mul]
          omega
      | incomplete =>
          simp [hkind]
          omega

private theorem incomplete_count_le_span
    (steps : List GreedyScheduleStep)
    (hprogress : ∀ step ∈ steps,
      step.kind = .incomplete → 1 ≤ step.spanDecrease) :
    (steps.map GreedyScheduleStep.kind).count .incomplete ≤
      (steps.map GreedyScheduleStep.spanDecrease).sum := by
  induction steps with
  | nil => simp
  | cons step steps ih =>
      have htail : ∀ tailStep ∈ steps,
          tailStep.kind = .incomplete → 1 ≤ tailStep.spanDecrease := by
        intro tailStep hmem
        exact hprogress tailStep (List.mem_cons_of_mem step hmem)
      have ih' := ih htail
      cases hkind : step.kind with
      | complete =>
          simp [hkind]
          omega
      | incomplete =>
          have hstep : 1 ≤ step.spanDecrease :=
            hprogress step List.mem_cons_self hkind
          simp [hkind]
          omega

/-- Forget metric magnitudes while deriving the global trace bounds from the
per-step progress and resource-budget obligations. -/
def trace (S : GreedyScheduleRun) : GreedyScheduleTrace where
  processors := S.processors
  totalWork := S.totalWork
  totalSpan := S.totalSpan
  steps := S.steps.map GreedyScheduleStep.kind
  processors_pos := S.processors_pos
  complete_work_bound :=
    (complete_count_mul_le_work S.processors S.steps S.complete_progress).trans
      S.work_budget
  incomplete_span_bound :=
    (incomplete_count_le_span S.steps S.incomplete_progress).trans S.span_budget

/-- The aggregate accounting certificate derived from local step progress. -/
def accounting (S : GreedyScheduleRun) : GreedyScheduleAccounting :=
  S.trace.accounting

/-- The per-step execution form of the greedy-scheduler bound:
`Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span (S : GreedyScheduleRun) :
    S.time ≤ S.totalWork / S.processors + S.totalSpan := by
  have h := S.trace.time_le_work_div_add_span
  simpa [time, GreedyScheduleTrace.time, trace] using h

end GreedyScheduleRun

namespace DAGSchedule

/-- Convert a type-safe DAG execution into the local per-step accounting
interface.  Both global budgets are derived by telescoping; neither is supplied
by the caller. -/
def toRun {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) (hprocessors : 0 < processors) :
    GreedyScheduleRun where
  processors := processors
  totalWork := G.remainingWork remaining
  totalSpan := G.remainingSpan remaining
  steps := D.metricSteps
  processors_pos := hprocessors
  work_budget := by
    have hbalance := D.work_balance
    omega
  span_budget := by
    have hbalance := D.span_balance
    omega
  complete_progress := all_complete_progress D
  incomplete_progress := all_incomplete_progress D

/-- Greedy-scheduler bound for a chained execution from an arbitrary residual
state. -/
theorem time_le_remainingWork_div_add_remainingSpan
    {G : CompDAG} {processors : ℕ} {remaining : ℕ → ℕ}
    (D : DAGSchedule G processors remaining) (hprocessors : 0 < processors) :
    D.time ≤ G.remainingWork remaining / processors + G.remainingSpan remaining := by
  have hbound := (D.toRun hprocessors).time_le_work_div_add_span
  simpa [time, toRun, GreedyScheduleRun.time] using hbound

/-- CLRS Theorems 27.1/27.2 for an explicit greedy execution of a computation
DAG: `Tₚ ≤ T₁ / p + T∞`. -/
theorem time_le_work_div_add_span {G : CompDAG} {processors : ℕ}
    (D : DAGSchedule G processors G.node_work) (hprocessors : 0 < processors) :
    D.time ≤ G.work / processors + G.span := by
  have hbound := D.time_le_remainingWork_div_add_remainingSpan hprocessors
  simpa [CompDAG.remainingWork, CompDAG.work, CompDAG.remainingSpan,
    CompDAG.withWork] using hbound

end DAGSchedule

/-! ## Spawn trees

The spawn/sync structure of a parallel divide-and-conquer computation.
A `spawn` node models one spawn/sync pair and contributes unit work and
unit critical-path overhead; a `seq` node is sequential composition. -/

inductive SpawnTree : Type where
  | leaf (w : ℕ) : SpawnTree
  | seq (t1 t2 : SpawnTree) : SpawnTree
  | spawn (t1 t2 : SpawnTree) : SpawnTree
deriving Repr

namespace SpawnTree

/-- The work of a spawn tree: leaf weights plus unit cost per spawn node. -/
def work : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => work t1 + work t2
  | spawn t1 t2 => work t1 + work t2 + 1

/-- The span of a spawn tree: sequential spans add; spawned children run in
parallel, so their spans take the maximum, plus unit spawn overhead. -/
def span : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => span t1 + span t2
  | spawn t1 t2 => max (span t1) (span t2) + 1

/-- T∞ ≤ T₁ for spawn trees. -/
theorem span_le_work : ∀ t : SpawnTree, t.span ≤ t.work
  | leaf w => Nat.le_refl w
  | seq t1 t2 => Nat.add_le_add (span_le_work t1) (span_le_work t2)
  | spawn t1 t2 => by
      have h1 := span_le_work t1
      have h2 := span_le_work t2
      simp only [span, work]
      omega

end SpawnTree

/-! ## Parallel loops

A parallel loop over `n` iterations is modeled as a balanced binary spawn
tree, matching the textbook's Θ(log n) overhead analysis. -/

/-- The spawn tree for a parallel loop with `n` iterations of weight `w`
each: a balanced binary spawn tree with `n` leaves. -/
def parallelLoopTree (n w : ℕ) : SpawnTree :=
  if n ≤ 1 then
    .leaf (n * w)
  else
    .spawn (parallelLoopTree (n / 2) w) (parallelLoopTree (n - n / 2) w)
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem parallelLoopTree_of_le_one {n w : ℕ} (hn : n ≤ 1) :
    parallelLoopTree n w = .leaf (n * w) := by
  rw [parallelLoopTree]
  simp [hn]

theorem parallelLoopTree_unfold {n w : ℕ} (hn : 2 ≤ n) :
    parallelLoopTree n w =
      .spawn (parallelLoopTree (n / 2) w) (parallelLoopTree (n - n / 2) w) := by
  rw [parallelLoopTree]
  simp [show ¬n ≤ 1 by omega]

/-- The work of a parallel loop: `n` iterations of weight `w` plus one unit
per internal spawn node (`n - 1` of them). -/
theorem parallelLoop_work {n : ℕ} (hn : 1 ≤ n) (w : ℕ) :
    (parallelLoopTree n w).work + 1 = n * w + n := by
  revert hn w
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn w
      by_cases h1 : n ≤ 1
      · have : n = 1 := by omega
        subst this
        simp [parallelLoopTree_of_le_one, SpawnTree.work]
      · rw [parallelLoopTree_unfold (by omega), SpawnTree.work]
        have h1 := ih (n / 2) (by omega) (by omega) w
        have h2 := ih (n - n / 2) (by omega) (by omega) w
        have hsum : n / 2 * w + (n - n / 2) * w = n * w := by
          rw [← Nat.add_mul]
          congr 1
          omega
        omega

/-- The spawn depth of the balanced parallel-loop tree: `0` for `n ≤ 1`,
else one more than the deeper of the two halves. -/
def parallelLoopDepth (n : ℕ) : ℕ :=
  if n ≤ 1 then
    0
  else
    max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) + 1
termination_by n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by norm_num)
  · exact Nat.sub_lt (by omega) (Nat.div_pos (by omega) (by norm_num))

theorem parallelLoopDepth_of_le_one {n : ℕ} (hn : n ≤ 1) :
    parallelLoopDepth n = 0 := by
  rw [parallelLoopDepth]
  simp [hn]

theorem parallelLoopDepth_unfold {n : ℕ} (hn : 2 ≤ n) :
    parallelLoopDepth n =
      max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) + 1 := by
  rw [parallelLoopDepth]
  simp [show ¬n ≤ 1 by omega]

/-- Exact span of the parallel-loop tree: one iteration's weight plus the
balanced halving depth. -/
theorem parallelLoop_span (n w : ℕ) :
    (parallelLoopTree n w).span =
      if n ≤ 1 then n * w else w + parallelLoopDepth n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [parallelLoopTree_of_le_one hn, if_pos hn]
        rfl
      · rw [parallelLoopTree_unfold (by omega), if_neg hn, SpawnTree.span,
          parallelLoopDepth_unfold (by omega)]
        rw [ih (n / 2) (by omega), ih (n - n / 2) (by omega)]
        by_cases h1 : n / 2 ≤ 1 <;> by_cases h2 : n - n / 2 ≤ 1
        · rw [if_pos h1, if_pos h2, parallelLoopDepth_of_le_one h1,
            parallelLoopDepth_of_le_one h2]
          have e1 : n / 2 * w = w := by
            have : n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          have e2 : (n - n / 2) * w = w := by
            have : n - n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e1, e2]
          simp
        · rw [if_pos h1, if_neg h2, parallelLoopDepth_of_le_one h1]
          have e1 : n / 2 * w = w := by
            have : n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e1]
          omega
        · rw [if_neg h1, if_pos h2, parallelLoopDepth_of_le_one h2]
          have e2 : (n - n / 2) * w = w := by
            have : n - n / 2 = 1 := by omega
            rw [this, Nat.one_mul]
          rw [e2]
          omega
        · rw [if_neg h1, if_neg h2]
          omega

/-- The depth is logarithmic: `n ≤ 2 ^ depth`. -/
theorem parallelLoopDepth_pow (n : ℕ) : n ≤ 2 ^ parallelLoopDepth n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ 1
      · rw [parallelLoopDepth_of_le_one hn, pow_zero]
        omega
      · rw [parallelLoopDepth_unfold (by omega), pow_succ]
        have h1 := ih (n / 2) (by omega)
        have h2 := ih (n - n / 2) (by omega)
        have hmax :
            2 ^ max (parallelLoopDepth (n / 2)) (parallelLoopDepth (n - n / 2)) =
              max (2 ^ parallelLoopDepth (n / 2))
                (2 ^ parallelLoopDepth (n - n / 2)) := by
          rcases le_total (parallelLoopDepth (n / 2))
            (parallelLoopDepth (n - n / 2)) with h | h
          · rw [max_eq_right h,
              max_eq_right (Nat.pow_le_pow_right (by norm_num) h)]
          · rw [max_eq_left h,
              max_eq_left (Nat.pow_le_pow_right (by norm_num) h)]
        rw [hmax]
        rcases le_total (2 ^ parallelLoopDepth (n / 2))
          (2 ^ parallelLoopDepth (n - n / 2)) with h | h
        · rw [max_eq_right h]
          omega
        · rw [max_eq_left h]
          omega

end Chapter27
end CLRS
