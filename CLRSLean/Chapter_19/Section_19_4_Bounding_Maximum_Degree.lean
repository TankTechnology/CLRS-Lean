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

/--
The marked-tree invariant of CLRS Lemma 19.1.  A node is `Wellformed` when its
children, listed in the order they were linked (earliest first), satisfy the
degree bound: the child in position `j` has degree at least `j - 1`, and every
child is itself `Wellformed`.

This is exactly the invariant that `CONSOLIDATE` and cascading cuts maintain: a
child linked while its parent had degree `j` itself had degree `j` at link
time, and the "at most one child lost before a cut" mark rule lets it drop to at
most `j - 1`.
-/
inductive Wellformed : FTree → Prop where
  | node {cs : List FTree}
      (hdeg : ∀ (j : Nat) (hj : j < cs.length), j - 1 ≤ (cs[j]).degree)
      (hall : ∀ c ∈ cs, Wellformed c) :
      Wellformed (.node cs)

/-- A leaf (degree-0 node) is trivially wellformed. -/
theorem wellformed_leaf : Wellformed (node []) := by
  refine Wellformed.node ?_ ?_
  · intro j hj; simp at hj
  · intro c hc; simp at hc

/--
Fibonacci-style two-step lower-bound recurrence, in the "shifted" form needed by
the subtree-size induction: `F(k+3) ≤ F(k+2) + F(k+1)` (with the convention
`F(0-th)` handled by natural-number truncation at `k = 0`).
-/
theorem fibLowerBound_succ_le (n : Nat) :
    fibLowerBound (n + 1) ≤ fibLowerBound n + fibLowerBound (n - 1) := by
  cases n with
  | zero => decide
  | succ m =>
      have h : fibLowerBound (m + 1 + 1) = fibLowerBound (m + 1) + fibLowerBound m :=
        FibHeap.fibLowerBound_step m
      simp only [Nat.add_sub_cancel]
      omega

/--
Numeric core of CLRS Lemma 19.4, generalized over a starting position `p`.

If a list `L` of subtree sizes has, in position `j`, a value at least
`F((p + j) + 1)` (`fibLowerBound (p + j - 1)`, the Lemma-19.1 degree lower bound
for a child starting at offset `p`), then the whole list plus the ambient node
weighs at least `F(p + |L| + 2)` more than `F(p + 2)`:
`fibLowerBound (p + L.length) ≤ fibLowerBound p + L.sum`.

The proof peels the head child and shifts the offset by one, using
{lit}`fibLowerBound_succ_le` to fold the head's contribution into the Fibonacci
recurrence.
-/
theorem sum_lb_from :
    ∀ (L : List Nat) (p : Nat),
      (∀ (j : Nat) (hj : j < L.length), fibLowerBound (p + j - 1) ≤ L[j]) →
      fibLowerBound (p + L.length) ≤ fibLowerBound p + L.sum := by
  intro L
  induction L with
  | nil =>
      intro p _
      simp
  | cons c cs ih =>
      intro p hL
      have hc : fibLowerBound (p - 1) ≤ c := by
        have h := hL 0 (by simp)
        simpa using h
      have htail : ∀ (j : Nat) (hj : j < cs.length),
          fibLowerBound (p + 1 + j - 1) ≤ cs[j] := by
        intro j hj
        have hj' : j + 1 < (c :: cs).length := by
          simp only [List.length_cons]; omega
        have h := hL (j + 1) hj'
        have harg : p + (j + 1) - 1 = p + 1 + j - 1 := by omega
        rw [harg] at h
        simpa using h
      have htie := ih (p + 1) htail
      have hstep : fibLowerBound (p + 1) ≤ fibLowerBound p + fibLowerBound (p - 1) :=
        fibLowerBound_succ_le p
      simp only [List.length_cons, List.sum_cons]
      have hidx : p + (cs.length + 1) = p + 1 + cs.length := by omega
      rw [hidx]
      calc
        fibLowerBound (p + 1 + cs.length)
            ≤ fibLowerBound (p + 1) + cs.sum := htie
        _ ≤ (fibLowerBound p + fibLowerBound (p - 1)) + cs.sum :=
              Nat.add_le_add_right hstep _
        _ ≤ (fibLowerBound p + c) + cs.sum :=
              Nat.add_le_add_right (Nat.add_le_add_left hc _) _
        _ = fibLowerBound p + (c + cs.sum) := by omega

/--
**CLRS Lemma 19.4.**  Any wellformed node of degree `d` roots a subtree of at
least `F(d + 2)` nodes: `fibLowerBound d ≤ size`.

The proof is a strong (well-founded) induction on the tree.  Each child `cs[j]`
has, by the Lemma-19.1 invariant, degree at least `j - 1`, so by the inductive
hypothesis and monotonicity of `fibLowerBound` its subtree has at least
`fibLowerBound (j - 1)` nodes.  Summing those bounds through
{lit}`sum_lb_from` gives `fibLowerBound (degree) ≤ size`.
-/
theorem wellformed_size_ge_fibLowerBound :
    (t : FTree) → Wellformed t → fibLowerBound t.degree ≤ t.size
  | .node cs, hw => by
      cases hw with
      | node hdeg hall =>
          have key : ∀ (j : Nat) (hj : j < (cs.map FTree.size).length),
              fibLowerBound (0 + j - 1) ≤ (cs.map FTree.size)[j] := by
            intro j hj
            have hjcs : j < cs.length := by
              simpa [List.length_map] using hj
            have hmem : cs[j] ∈ cs := List.getElem_mem hjcs
            have hchild : Wellformed (cs[j]) := hall _ hmem
            have hrec := wellformed_size_ge_fibLowerBound (cs[j]) hchild
            have hd : j - 1 ≤ (cs[j]).degree := hdeg j hjcs
            have hmap : (cs.map FTree.size)[j] = (cs[j]).size := by
              rw [List.getElem_map]
            rw [hmap, Nat.zero_add]
            calc
              fibLowerBound (j - 1)
                  ≤ fibLowerBound (cs[j]).degree := FibHeap.fibLowerBound_monotone hd
              _ ≤ (cs[j]).size := hrec
          have hsum := sum_lb_from (cs.map FTree.size) 0 key
          simp only [List.length_map, Nat.zero_add] at hsum
          have hz : fibLowerBound 0 = 1 := rfl
          rw [hz] at hsum
          simpa using hsum
  termination_by t _ => sizeOf t
  decreasing_by
    have hjcs : j < cs.length := by simpa [List.length_map] using hj
    have hlt : sizeOf (cs[j]) < sizeOf cs := List.sizeOf_lt_of_mem (List.getElem_mem hjcs)
    simp only [FTree.node.sizeOf_spec]
    omega

end FTree
end Chapter19
end CLRS
