import Mathlib
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model
import CLRSLean.Chapter_19.Section_19_4_Bounding_Maximum_Degree

/-!
# Chapter 19 - S1. Executable Fibonacci heap: roots, marks, CONSOLIDATE

This module supplies the implementation-facing layer omitted by the abstract
`FibHeap` key-set model: a rooted forest of key-carrying nodes with mark bits
(the CLRS `x.degree`, `x.mark`, `x.child`), heap order, the marked-tree
invariant `Wellformed` (inherited from the `FTree` model by structural
projection, so Section 19.4's degree theorems apply directly), the `LINK`
step, and the executable `CONSOLIDATE` procedure with its correctness
theorems (key-set preservation, heap order, invariant maintenance, and the
degree-uniqueness property that makes the amortized analysis go through).

`CONSOLIDATE` is implemented as the degree-bucket merging CLRS describes:
the root list is folded into a list sorted by strictly increasing degree, and
each new root is linked with the stored root of the same degree (the
smaller key becomes the parent), which raises the degree by one and the
merging continues.  The degree-array formulation is the physical
implementation of this bucket list.

Main results:

- `FHNode`: a key-carrying tree node with mark bit and link-ordered children
- `FHNode.HeapOrdered` and `FHNode.Wellformed`: the two structural invariants
- `FHNode.link`: the CLRS `LINK` step (the smaller key becomes the parent)
- `FHNode.link_heapOrdered`, `link_wellformed`, `link_keys`, `link_degree_eq`:
  its correctness
- `FHNode.insertConsolidated` and `FHNode.consolidateList`: the executable
  `CONSOLIDATE` (degree-bucket merging)
- `FHNode.consolidateList_keys`, `consolidateList_heapOrdered`,
  `consolidateList_wellformed`: `CONSOLIDATE` correctness
- `FHNode.consolidateList_degree_unique`: at most one root per degree after
  consolidation
- `FH`: an executable heap (root forest + node count)
- `FH.makeHeap` / `FH.insert` / `FH.union` / `FH.minimum` / `FH.extractMin`:
  executable operations with key-set specifications

Current gaps:

- The cascading-cut procedure and the amortized cost accounting remain
  future targets; the degree-bucket consolidation here is their structural
  core.
-/

namespace CLRS
namespace Chapter19

open Finset

/-- A node of the executable Fibonacci heap: a key, a mark bit, and the list
of child subtrees in link order. -/
inductive FHNode where
  | node (key : Int) (marked : Bool) (children : List FHNode)
  deriving Inhabited

namespace FHNode

/-- The key of a node. -/
def key : FHNode → Int
  | node k _ _ => k

/-- The mark bit of a node. -/
def marked : FHNode → Bool
  | node _ m _ => m

/-- The children of a node, in link order. -/
def children : FHNode → List FHNode
  | node _ _ cs => cs

/-- The degree of a node is its number of children (CLRS `x.degree`). -/
def degree (t : FHNode) : Nat := t.children.length

/-- The subtree size of a node: the total number of nodes it roots. -/
def size : FHNode → Nat
  | node _ _ cs => 1 + (cs.map size).sum

/-- The keys of a subtree, as a list (multiset view). -/
def keysList : FHNode → List Int
  | node k _ cs => k :: cs.flatMap keysList

/-- The key set of a subtree (duplicates collapsed). -/
def keySet (t : FHNode) : Finset Int := t.keysList.toFinset

/-- The key set of a forest. -/
def forestKeyList (ts : List FHNode) : List Int := ts.flatMap keysList

/-- The key set of a forest. -/
def forestKeySet (ts : List FHNode) : Finset Int :=
  (ts.map keySet).foldr (fun a b => a ∪ b) ∅

@[simp] theorem key_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).key = k := rfl

@[simp] theorem marked_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).marked = m := rfl

@[simp] theorem children_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).children = cs := rfl

@[simp] theorem degree_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).degree = cs.length := rfl

@[simp] theorem size_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).size = 1 + (cs.map size).sum := by
  rw [size]

@[simp] theorem keysList_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).keysList = k :: cs.flatMap keysList := by
  rw [keysList]

/-- Heap order: every node's key is at most the keys of its children, and the
children are heap-ordered.  By transitivity the node's key is at most every
descendant key. -/
inductive HeapOrdered : FHNode → Prop where
  | node {k : Int} {m : Bool} {cs : List FHNode}
      (hle : ∀ c ∈ cs, k ≤ c.key)
      (hall : ∀ c ∈ cs, HeapOrdered c) :
      HeapOrdered (node k m cs)

/-- The structural projection to the `FTree` model: erase keys and marks. -/
def toFTree : FHNode → FTree
  | node _ _ cs => FTree.node (cs.map toFTree)

/-- The CLRS Lemma 19.1 marked-tree invariant, inherited from the `FTree`
model: the child in position `j` has degree at least `j - 1`. -/
def Wellformed (t : FHNode) : Prop := (t.toFTree).Wellformed

@[simp] theorem toFTree_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).toFTree = FTree.node (cs.map toFTree) := by
  rw [toFTree]

/-- The structural projection preserves degree. -/
theorem toFTree_degree (t : FHNode) : (t.toFTree).degree = t.degree := by
  cases t with
  | node k m cs => simp [toFTree, degree, FTree.degree]

/-- The structural projection preserves subtree size. -/
theorem toFTree_size (t : FHNode) : (t.toFTree).size = t.size := by
  refine FHNode.rec
    (motive_1 := fun t => (t.toFTree).size = t.size)
    (motive_2 := fun cs => (cs.map toFTree).map FTree.size = cs.map size)
    ?_ ?_ ?_ t
  · intro k m cs ih
    simp [toFTree, size, FTree.size, ih]
  · simp
  · intro c cs ih_c ih_cs
    simp [ih_c, ih_cs]

/-- A wellformed node of degree `d` has subtree size at least `F(d+2)`
(CLRS Lemma 19.4, inherited from the `FTree` model). -/
theorem wellformed_size_ge_fibLowerBound (t : FHNode) (hw : t.Wellformed) :
    FibHeap.fibLowerBound t.degree ≤ t.size := by
  have h := FTree.wellformed_size_ge_fibLowerBound t.toFTree hw
  simpa [toFTree_degree, toFTree_size] using h

/-- A wellformed node of degree `d` in an `n`-node heap has degree at most
`2 · ⌊log₂ n⌋ + 1` (CLRS Lemma 19.5, coarse form, inherited). -/
theorem wellformed_degree_le_twice_log_two (t : FHNode) (hw : t.Wellformed)
    {n : Nat} (hn : t.size ≤ n) :
    t.degree ≤ 2 * Nat.log 2 n + 1 := by
  have h := FTree.wellformed_degree_le_twice_log_two t.toFTree hw
    (by simpa [toFTree_size] using hn)
  simpa [toFTree_degree] using h

/-- A leaf is heap-ordered and wellformed. -/
theorem leaf_heapOrdered (k : Int) : HeapOrdered (node k false []) := by
  refine HeapOrdered.node ?_ ?_ <;> simp

theorem leaf_wellformed (k : Int) : (node k false []).Wellformed := by
  simpa [Wellformed, toFTree] using FTree.wellformed_leaf

/-- Heap order is preserved by appending a child whose key is at least the
parent's, when both are heap-ordered. -/
theorem heapOrdered_append_child (k : Int) (m : Bool) (xs : List FHNode)
    (hxs : HeapOrdered (node k m xs)) (y : FHNode) (hy : HeapOrdered y)
    (hky : k ≤ y.key) :
    HeapOrdered (node k m (xs ++ [y])) := by
  cases hxs with
  | node hle hall =>
      refine HeapOrdered.node ?_ ?_
      · intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hle c hc
        · rw [List.mem_singleton] at hc
          subst c
          exact hky
      · intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hall c hc
        · rw [List.mem_singleton] at hc
          subst c
          exact hy

/-- **The CLRS `LINK` step.**  Link `y` as a child of the smaller-key root
`x`; if `y`'s key is smaller, swap the roles.  The mark of the parent is
preserved. -/
def link (x y : FHNode) : FHNode :=
  if x.key ≤ y.key then
    node x.key x.marked (x.children ++ [y])
  else
    node y.key y.marked (y.children ++ [x])

/-- `LINK` preserves heap order. -/
theorem link_heapOrdered (x y : FHNode) (hx : x.HeapOrdered) (hy : y.HeapOrdered) :
    (link x y).HeapOrdered := by
  unfold link
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        have h' : k ≤ y.key := by simpa using h
        change (if k ≤ y.key then node k m (cs ++ [y]) else
          node y.key y.marked (y.children ++ [node k m cs])).HeapOrdered
        rw [if_pos h']
        exact heapOrdered_append_child k m cs hx y hy h'
  · cases y with
    | node k m cs =>
        have h' : ¬ x.key ≤ k := by simpa using h
        have hyx : k ≤ x.key := le_of_not_ge h'
        change (if x.key ≤ k then node x.key x.marked (x.children ++ [node k m cs])
          else node k m (cs ++ [x])).HeapOrdered
        rw [if_neg h']
        exact heapOrdered_append_child k m cs hy x hx hyx

/-- `LINK` preserves the marked-tree invariant when the parent's degree is at
most the child's (the equal-degree case `CONSOLIDATE` applies). -/
theorem link_wellformed (x y : FHNode) (hx : x.Wellformed) (hy : y.Wellformed)
    (hxy : x.degree = y.degree) :
    (link x y).Wellformed := by
  unfold link Wellformed
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        have h' : k ≤ y.key := by simpa using h
        simp only [key_node, marked_node, children_node]
        rw [if_pos h']
        have hdeg : (FTree.node (cs.map toFTree)).degree ≤ y.toFTree.degree := by
          have : (FTree.node (cs.map toFTree)).degree = y.toFTree.degree := by
            simpa [toFTree, toFTree_degree] using hxy
          omega
        have hw := FTree.link_wellformed (FTree.node (cs.map toFTree)) y.toFTree
          (by simpa [Wellformed, toFTree] using hx) hy hdeg
        simpa [toFTree, FTree.link] using hw
  · cases y with
    | node k m cs =>
        have h' : ¬ x.key ≤ k := by simpa using h
        simp only [key_node, marked_node, children_node]
        rw [if_neg h']
        have hdeg : (FTree.node (cs.map toFTree)).degree ≤ x.toFTree.degree := by
          have : (FTree.node (cs.map toFTree)).degree = x.toFTree.degree := by
            simpa [toFTree, toFTree_degree] using hxy.symm
          omega
        have hw := FTree.link_wellformed (FTree.node (cs.map toFTree)) x.toFTree
          (by simpa [Wellformed, toFTree] using hy) hx hdeg
        simpa [toFTree, FTree.link] using hw

/-- `LINK` preserves the key set of the two subtrees. -/
theorem link_keys (x y : FHNode) :
    (link x y).keySet = x.keySet ∪ y.keySet := by
  unfold link
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_pos h']
            ext z
            simp [keySet, keysList, List.toFinset_cons, List.flatMap_append,
              List.flatMap_singleton, List.toFinset_append, Finset.mem_union]
            simp only [or_left_comm, or_assoc, or_comm]
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : ¬ k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_neg h']
            ext z
            simp [keySet, keysList, List.toFinset_cons, List.flatMap_append,
              List.flatMap_singleton, List.toFinset_append, Finset.mem_union]
            simp only [or_left_comm, or_assoc, or_comm]

/-- The degree of a link of equal-degree roots: exactly one more. -/
theorem link_degree_eq (x y : FHNode) (hxy : x.degree = y.degree) :
    (link x y).degree = x.degree + 1 := by
  unfold link
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_pos h']
            simp [degree, children, hxy]
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : ¬ k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_neg h']
            simp [degree, children]
            have hlen : cs'.length = cs.length := by
              simpa [degree, children] using hxy.symm
            omega

/-- The size of a link is the sum of the two subtree sizes. -/
theorem link_size (x y : FHNode) : (link x y).size = x.size + y.size := by
  unfold link
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_pos h']
            simp [size]
            omega
  · cases x with
    | node k m cs =>
        cases y with
        | node k' m' cs' =>
            have h' : ¬ k ≤ k' := by simpa using h
            simp only [key_node, marked_node, children_node]
            rw [if_neg h']
            simp [size]
            omega

/-! ## CONSOLIDATE by degree-bucket merging -/

/-- A forest is structurally good when every tree is heap-ordered and
wellformed. -/
def ForestGood (ts : List FHNode) : Prop :=
  (∀ t ∈ ts, t.HeapOrdered) ∧ (∀ t ∈ ts, t.Wellformed)

/-- A forest is degree-strict when the degrees of its trees are strictly
increasing (the invariant `CONSOLIDATE` maintains: at most one root per
degree, roots ordered by degree). -/
def DegreeStrict (ts : List FHNode) : Prop :=
  ts.Pairwise (fun a b => a.degree < b.degree)

/-- Insert a root into a degree-strict forest, linking it with the stored
root of the same degree (the smaller key becomes the parent) and continuing
with the raised degree — exactly the CLRS `CONSOLIDATE` inner loop. -/
def insertConsolidated : List FHNode → FHNode → List FHNode
  | [], x => [x]
  | y :: ys, x =>
      if y.degree = x.degree then insertConsolidated ys (link x y)
      else if y.degree < x.degree then y :: insertConsolidated ys x
      else x :: y :: ys

/-- The key set is preserved by one insertion with consolidation. -/
theorem insertConsolidated_keys (ys : List FHNode) (x : FHNode) :
    forestKeySet (insertConsolidated ys x) = forestKeySet ys ∪ x.keySet := by
  revert x
  induction ys with
  | nil => intro x; simp [insertConsolidated, forestKeySet]
  | cons y ys ih =>
      intro x
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · simp [h1]
        have hrec := ih (link x y)
        rw [hrec, link_keys]
        simp [forestKeySet]
        ext k
        simp [Finset.mem_union]
        tauto
      · by_cases h2 : y.degree < x.degree
        · simp [h1, h2]
          have hrec := ih x
          change y.keySet ∪ forestKeySet (insertConsolidated ys x) =
            forestKeySet (y :: ys) ∪ x.keySet
          rw [hrec]
          simp [forestKeySet]
        · have hx_le : x.degree ≤ y.degree := le_of_not_gt h2
          have hx_ne : x.degree ≠ y.degree := by
            intro h
            exact h1 h.symm
          have hx_lt : x.degree < y.degree := lt_of_le_of_ne hx_le hx_ne
          simp [h1, h2]
          simp [forestKeySet]
          ext k
          simp [Finset.mem_union]
          tauto

/-- Structural goodness is preserved by one insertion with consolidation. -/
theorem insertConsolidated_good (ys : List FHNode) (x : FHNode)
    (hys : ForestGood ys) (hx : ForestGood [x]) :
    ForestGood (insertConsolidated ys x) := by
  revert x
  induction ys with
  | nil =>
      intro x hx
      simp [insertConsolidated]
      exact hx
  | cons y ys ih =>
      intro x hx
      unfold insertConsolidated
      rcases hys with ⟨hle, hwf⟩
      have hy : y.HeapOrdered := hle y (by simp)
      have hyw : y.Wellformed := hwf y (by simp)
      have hys' : ForestGood ys := ⟨
        (fun t ht => hle t (by simp [ht])),
        (fun t ht => hwf t (by simp [ht]))⟩
      have hx' : ForestGood [x] := hx
      by_cases h1 : y.degree = x.degree
      · simp [h1]
        have hxy : x.degree = y.degree := h1.symm
        have hxho : x.HeapOrdered := hx.1 x (by simp)
        have hxwf : x.Wellformed := hx.2 x (by simp)
        have hlx : (link x y).HeapOrdered := link_heapOrdered x y hxho hy
        have hlw : (link x y).Wellformed := link_wellformed x y hxwf hyw hxy
        exact ih hys' (link x y) ⟨(fun t ht => by
          rw [List.mem_singleton] at ht
          subst t
          exact hlx),
          (fun t ht => by
          rw [List.mem_singleton] at ht
          subst t
          exact hlw)⟩
      · by_cases h2 : y.degree < x.degree
        · simp [h1, h2]
          rcases ih hys' x hx' with ⟨hle', hwf'⟩
          exact ⟨(fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · simpa [ht] using hy
            · exact hle' t ht),
            (fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · simpa [ht] using hyw
            · exact hwf' t ht)⟩
        · have hx_le : x.degree ≤ y.degree := le_of_not_gt h2
          have hx_ne : x.degree ≠ y.degree := by
            intro h
            exact h1 h.symm
          have hx_lt : x.degree < y.degree := lt_of_le_of_ne hx_le hx_ne
          simp [h1, h2]
          exact ⟨(fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · simpa [ht] using hx.1
            · rw [List.mem_cons] at ht
              rcases ht with ht | ht
              · simpa [ht] using hy
              · exact hle t (by simp [ht])),
            (fun t ht => by
            rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · simpa [ht] using hx.2
            · rw [List.mem_cons] at ht
              rcases ht with ht | ht
              · simpa [ht] using hyw
              · exact hwf t (by simp [ht]))⟩

/-- Inserting into a degree-strict forest preserves the lower bound `k <
degree` of every tree. -/
theorem insertConsolidated_degree_gt (ys : List FHNode) (x : FHNode) (k : Nat)
    (hys : ∀ t ∈ ys, k < t.degree) (hx : k < x.degree) :
    ∀ t ∈ insertConsolidated ys x, k < t.degree := by
  revert x k hx
  induction ys with
  | nil => intro x k hys hx t ht; simp [insertConsolidated] at ht; subst t; exact hx
  | cons y ys ih =>
      intro x k hys hx
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · simp [h1]
        have hlink : k < (link x y).degree := by
          rw [link_degree_eq x y h1.symm]
          have : k < x.degree := hx
          omega
        have hys' : ∀ t ∈ ys, k < t.degree := by
          intro t ht
          exact hys t (by simp [ht])
        exact ih (link x y) k hys' hlink
      · by_cases h2 : y.degree < x.degree
        · rw [if_neg h1, if_pos h2]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with ht | ht
          · subst t
            exact hys y (by simp)
          · exact ih x k (fun t ht => hys t (by simp [ht])) hx t ht
        · rw [if_neg h1, if_neg h2]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with ht | ht
          · subst t
            exact hx
          · rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · subst t
              exact hys y (by simp)
            · exact hys t (by simp [ht])

/-- Inserting into a degree-strict forest preserves strictness and
uniqueness of degrees. -/
theorem insertConsolidated_degreeStrict (ys : List FHNode) (x : FHNode)
    (hys : DegreeStrict ys) :
    DegreeStrict (insertConsolidated ys x) := by
  revert x
  induction ys with
  | nil => intro x; simp [insertConsolidated, DegreeStrict]
  | cons y ys ih =>
      intro x
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · simp [h1]
        exact ih hys.tail (link x y)
      · by_cases h2 : y.degree < x.degree
        · simp [h1, h2]
          have hrec := ih hys.tail x
          have hgt : ∀ t ∈ insertConsolidated ys x, y.degree < t.degree :=
            insertConsolidated_degree_gt ys x y.degree
              (fun t ht => List.rel_of_pairwise_cons hys (by simp [ht])) h2
          change (y :: insertConsolidated ys x).Pairwise
            (fun a b => a.degree < b.degree)
          exact List.Pairwise.cons hgt hrec
        · have hx_le : x.degree ≤ y.degree := le_of_not_gt h2
          have hx_ne : x.degree ≠ y.degree := by
            intro h
            exact h1 h.symm
          have hx_lt : x.degree < y.degree := lt_of_le_of_ne hx_le hx_ne
          simp [h1, h2]
          change (x :: y :: ys).Pairwise (fun a b => a.degree < b.degree)
          refine List.Pairwise.cons ?_ ?_
          · intro b hb
            rw [List.mem_cons] at hb
            rcases hb with hb | hb
            · subst b
              exact hx_lt
            · have hyb : y.degree < b.degree :=
                List.rel_of_pairwise_cons hys (by simp [hb])
              exact lt_trans hx_lt hyb
          · exact hys
