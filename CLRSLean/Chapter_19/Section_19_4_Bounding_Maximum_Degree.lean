import Mathlib
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model

/-!
# CLRS Section 19.4 - Bounding the maximum degree

This section proves the combinatorial heart of the Fibonacci-heap analysis:
a node of degree `d` roots a subtree of at least `F(d+2)` nodes, hence the
maximum degree in an `n`-node heap is `O(log n)` and, sharply,
`D(n) ≤ ⌊log_φ n⌋` where `φ = (1 + √5)/2`.  This is CLRS Lemma 19.1, Lemma 19.4
and Lemma 19.5 (Section 19.4).

We work over an abstract rooted-tree model.  A Fibonacci-heap tree is a node
carrying an ordered list of child subtrees.  The invariant maintained by
`CONSOLIDATE` (equal-degree linking) and cascading cuts is captured by
{lit}`CLRS.Chapter19.FTree.Wellformed`: if the children of a node are listed in
the order they were linked, then the child in position `j` has degree at least
`j - 1`.  This is exactly CLRS Lemma 19.1 (a child linked when its parent had
degree `j` itself had degree `j` at link time, and the "at most one child lost"
mark invariant lets it drop to `j - 1`).

Main results:

- {lit}`CLRS.Chapter19.FTree.Wellformed`: the CLRS Lemma 19.1 marked-tree
  invariant ("at most one child lost").
- {lit}`CLRS.Chapter19.FTree.wellformed_size_ge_fibLowerBound`: **CLRS Lemma
  19.4** — a wellformed node of degree `d` has subtree size at least
  `F(d+2)` (`fibLowerBound d`).
- {lit}`CLRS.Chapter19.FTree.goldenRatio_pow_le_fibLowerBound`: `φ^d ≤ F(d+2)`.
- {lit}`CLRS.Chapter19.FTree.wellformed_goldenRatio_pow_le_size`: `φ^d ≤ size`.
- {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_logb`: **CLRS Lemma 19.5** —
  a wellformed node of degree `d` in an `n`-node heap satisfies
  `d ≤ log_φ n`.
- {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_floor_logb`: the sharp CLRS
  form `d ≤ ⌊log_φ n⌋`.
- {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_twice_log_two`: the coarse
  natural-number budget `d ≤ 2 · ⌊log₂ n⌋ + 1`.

Current gaps:

- The executable pointer forest, the destructive `CONSOLIDATE` and cascading-cut
  procedures, and the amortized-cost accounting remain future refinement
  targets.  This file seals the structural degree bound they rely on.

Notation conventions used in this section:

- `t` : a rooted Fibonacci-heap tree
- `d`, `k` : node degree (number of children)
- `F(d+2)` : the `(d+2)`-nd Fibonacci number, here {lit}`fibLowerBound d`
- `φ` : the golden ratio `(1 + √5)/2`
-/

namespace CLRS
namespace Chapter19

open FibHeap (fibLowerBound)

/--
Abstract rooted tree of a Fibonacci heap: a node carrying an ordered list of
child subtrees.  Children are recorded in the order they were linked to the
node (earliest first), which is the order CLRS Lemma 19.1 refers to.
-/
inductive FTree where
  | node : List FTree → FTree
  deriving Inhabited

namespace FTree

/-- The children of a node, in link order. -/
def children : FTree → List FTree
  | .node cs => cs

/-- The degree of a node is its number of children (CLRS `x.degree`). -/
def degree (t : FTree) : Nat := t.children.length

/-- The subtree size of a node: the total number of nodes it roots
(CLRS `size(x)`). -/
def size : FTree → Nat
  | .node cs => 1 + (cs.map size).sum

@[simp] theorem children_node (cs : List FTree) : (node cs).children = cs := rfl

@[simp] theorem degree_node (cs : List FTree) : (node cs).degree = cs.length := rfl

@[simp] theorem size_node (cs : List FTree) :
    (node cs).size = 1 + (cs.map size).sum := by
  rw [size]

end FTree
end Chapter19
end CLRS
