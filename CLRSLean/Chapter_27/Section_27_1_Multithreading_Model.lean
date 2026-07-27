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
- `SpawnTree.span_le_work`: the same inequality for spawn trees.
- `parallelLoop_work`: the work of the parallel-loop tree is exactly
  `n * w + (n - 1)`.
- `parallelLoop_span`: the span is exactly `w + parallelLoopDepth n` for
  `n ≥ 2`, where `parallelLoopDepth` is the balanced halving depth.
- `parallelLoopDepth_pow`: `n ≤ 2 ^ parallelLoopDepth n`, the
  span-is-logarithmic direction.

## Deferred work

* The greedy-scheduler bound (CLRS Theorem 27.1/27.2, `Tp ≤ T₁/p + T∞`)
  requires an explicit time-step execution model and is not claimed here.
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

end CompDAG

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
