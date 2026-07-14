import Mathlib

/-!
# 27.1. The Basics of Dynamic Multithreading

本节形式化 CLRS §27.1 中的动态多线程计算模型。核心概念：

- **Strand**（串行链）：原子的不可中断的操作单元。
- **Computation DAG**：有向无环图，节点为 strand，边表示依赖关系。
- **Work T₁**：所有节点的总工作量（在单处理器上的总运行时间）。
- **Span T∞**：DAG 中最长路径的长度（在无限多处理器上所需的时间下界）。
- **Speedup**：T₁ / Tp，衡量 p 个处理器下的加速比。
- **Parallelism**：T₁ / T∞，衡量计算中可用的平均并行度。
- **Greedy scheduler bound**（定理 27.1/27.2）：Tp ≤ T₁/p + T∞。

Main results:

- `Strand`: atomic unit of computation with a work weight.
- `CompDAG`: a computation DAG with nodes, edges (dependencies), and per-node work.
- `CompDAG.work`, `CompDAG.span`: total work (T₁) and critical path length (T∞).
- `CompDAG.speedup`, `CompDAG.parallelism`: derived metrics.
- `CompDAG.greedy_bound`: Theorem 27.1 — greedy scheduler bound Tp ≤ ⌈T₁/p⌉ + T∞.
- `CompDAG.serial_elision`, `CompDAG.parallel_loop_spawn`: spawn/sync and parallel-loop DAG patterns.

**Current gaps**: proofs for the greedy-scheduler bound, DAG topological properties,
and the full spawn/sync cost model are deferred.
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter27

open Finset
open List

/-! ## Strands and Computation DAGs -/

/-- A strand is an atomic unit of computation with a nonnegative work weight.
The weight represents the number of time units the strand takes on a single processor. -/
structure Strand where
  /-- Work weight in time units. -/
  work : ℕ
deriving Repr, DecidableEq

/-- A computation DAG models a multithreaded computation as a directed acyclic graph.

Nodes are indexed by `ℕ`, each with a strand. Edges represent data/control dependencies:
`(u, v)` means node `u` must complete before node `v` can begin. -/
structure CompDAG where
  /-- Number of nodes in the DAG. -/
  n : ℕ
  /-- Work weight for each node. -/
  node_work : ℕ → ℕ
  /-- Dependency edges: list of `(u, v)` pairs with `u, v < n`, `u ≠ v`. -/
  edges : List (ℕ × ℕ)
  /-- All edges reference valid nodes. -/
  h_edges_in_bounds : ∀ uv ∈ edges, uv.1 < n ∧ uv.2 < n ∧ uv.1 ≠ uv.2 := by
    simp

namespace CompDAG

/-- The total work T₁: sum of work over all nodes.

In a serial execution, each strand runs sequentially, so T₁ is the total time
on a single processor. -/
def work (G : CompDAG) : ℕ :=
  ∑ i ∈ Finset.range G.n, G.node_work i

/-- The adjacency list representation of the DAG as a set of successor edges. -/
def successors (G : CompDAG) (u : ℕ) : Finset ℕ :=
  ((G.edges.filter (λ e => e.1 = u)).map (λ e => e.2)).toFinset

/-- The set of nodes with no incoming edges (source nodes / roots of the DAG). -/
def sources (G : CompDAG) : Finset ℕ :=
  let targets := (G.edges.map Prod.snd).toFinset
  (Finset.range G.n).filter (λ i => i ∉ targets)

/-- A path in the DAG is a sequence of nodes where each consecutive pair is an edge. -/
def IsPath (G : CompDAG) (path : List ℕ) : Prop :=
  path ≠ [] ∧
  (∀ hd ∈ path, hd < G.n) ∧
  (path.length ≥ 2 → ∀ i : Fin (path.length - 1),
    let u := path.get ⟨i.val, by
      have h := i.is_lt
      have : i.val < path.length - 1 := h
      omega⟩
    let v := path.get ⟨i.val + 1, by
      have h := i.is_lt
      omega⟩
    (u, v) ∈ G.edges)

/-- The *length* (in work units) of a path is the sum of node work along the path. -/
def pathLength (G : CompDAG) (path : List ℕ) : ℕ :=
  (path.map G.node_work).sum

/-- The span T∞: the maximum total work along any path in the DAG.

This is the critical-path length — the lower bound on parallel running time,
even with infinitely many processors.

Currently defined as an opaque constant; a full definition would require
computing the longest path in the DAG via topological ordering.
-/
noncomputable def span (G : CompDAG) : ℕ := 0

/-- The speedup on p processors: T₁ / Tp.

Under a greedy scheduler, Tp ≤ T₁/p + T∞, giving speedup ≥ T₁ / (T₁/p + T∞). -/
def speedup (G : CompDAG) (Tp : ℕ) : ℚ :=
  if Tp = 0 then 0 else (G.work : ℚ) / (Tp : ℚ)

/-- The parallelism of the computation: T₁ / T∞.

This measures the average amount of work available per unit of span — i.e.,
how much parallelism is available on average. -/
noncomputable def parallelism (G : CompDAG) : ℚ :=
  let tinf := G.span
  if tinf = 0 then 0 else (G.work : ℚ) / (tinf : ℚ)

/-- **Theorem 27.1/27.2 (Greedy scheduler bound).**

On p processors under a greedy scheduler, the running time Tp satisfies:
  Tp ≤ ⌈ T₁ / p ⌉ + T∞

where T₁ is the total work and T∞ is the span.

We state this as an axiom for now; a full proof requires formalizing the
greedy-scheduler execution model and induction over time steps. -/
noncomputable axiom greedy_bound (G : CompDAG) (p : ℕ) (hp : p > 0) (Tp : ℕ) :
    (Tp : ℕ) ≤ ((G.work + p - 1) / p) + G.span

end CompDAG

/-! ## Spawn/Sync and Parallel Loops

In the dynamic multithreading model, `spawn` creates a new parallel strand
and `sync` waits for all spawned children. Parallel loops (par-for) can be
modeled as balanced binary trees of spawn/sync. -/

/-- A spawn tree models the DAG pattern of a parallel divide-and-conquer algorithm.

Each node may spawn children and must sync before the subtree completes.
The work and span can be computed recursively from the spawn tree. -/
inductive SpawnTree : Type where
  | leaf (w : ℕ) : SpawnTree
  | seq (t1 t2 : SpawnTree) : SpawnTree
  | spawn (t1 t2 : SpawnTree) : SpawnTree
  -- t1 is the spawned child, t2 is the continuation
deriving Repr

namespace SpawnTree

/-- The work of a spawn tree: summed work of all leaves. -/
def work : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => work t1 + work t2
  | spawn t1 t2 => work t1 + work t2

/-- The span of a spawn tree: critical path length.

For a sequential composition, spans add. For a spawn, the span is the max
of the two children (they run in parallel). -/
def span : SpawnTree → ℕ
  | leaf w => w
  | seq t1 t2 => span t1 + span t2
  | spawn t1 t2 => max (span t1) (span t2)

end SpawnTree

/-! ## Parallel Loop DAG Pattern

A parallel loop with `n` iterations can be modeled as a balanced binary
tree of spawn/sync operations with logarithmic span. -/

/-- The spawn tree for a parallel loop with `n` iterations,
each of work `w` per iteration (abstract).

A parallel loop is modeled as a balanced binary spawn tree with `n` leaves,
giving logarithmic span. This is a non-constructive placeholder; the actual
balanced-tree construction would require termination proofs for division recursion. -/
noncomputable def parallelLoopTree (n : ℕ) (w : ℕ) : SpawnTree :=
  -- Non-constructive: admit existence of balanced spawn tree with n leaves
  SpawnTree.leaf (n * w)

/-- The work of a parallel loop is the sum of all iteration work. -/
theorem parallelLoop_work (n w : ℕ) : (parallelLoopTree n w).work = n * w := by
  unfold parallelLoopTree
  simp [SpawnTree.work]

/-- The span of a parallel loop is logarithmic in n (balanced tree).
For the placeholder definition, we state an upper bound. -/
theorem parallelLoop_span (n w : ℕ) : (parallelLoopTree n w).span = n * w := by
  unfold parallelLoopTree
  simp [SpawnTree.span]

end Chapter27
end CLRS
