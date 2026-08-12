import Mathlib.Tactic

/-!
# 26.1 S1. Computation DAGs

The foundational dynamic-multithreading model: strands, computation DAGs,
work, span, speedup, and parallelism.
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
end Chapter27
end CLRS
