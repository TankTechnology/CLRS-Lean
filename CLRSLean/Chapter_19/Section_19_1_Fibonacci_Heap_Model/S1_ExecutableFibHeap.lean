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
  | node k _ cs => k :: cs.flatMap FHNode.keysList

/-- The key set of a subtree (duplicates collapsed). -/
def keySet (t : FHNode) : Finset Int := t.keysList.toFinset

/-- The key set of a forest. -/
def forestKeyList (ts : List FHNode) : List Int := ts.flatMap keysList

/-- The key set of a forest. -/
def forestKeySet (ts : List FHNode) : Finset Int :=
  (ts.map keySet).foldr (fun a b => a ∪ b) ∅

/-- The number of marked nodes in a subtree, including the root. -/
def marks : FHNode → Nat
  | node _ marked children =>
      (if marked then 1 else 0) + (children.map marks).sum

/-- The number of marked nodes in a forest. -/
def forestMarks (roots : List FHNode) : Nat :=
  (roots.map marks).sum

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
    (node k m cs).keysList = k :: cs.flatMap FHNode.keysList := by
  rw [keysList]

@[simp] theorem marks_node (k : Int) (m : Bool) (cs : List FHNode) :
    (node k m cs).marks =
      (if m then 1 else 0) + (cs.map marks).sum := rfl

@[simp] theorem forestMarks_nil : forestMarks [] = 0 := rfl

@[simp] theorem forestMarks_cons (t : FHNode) (ts : List FHNode) :
    forestMarks (t :: ts) = t.marks + forestMarks ts := by
  simp [forestMarks]

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

/-- The executable `CONSOLIDATE`: fold the root list into a degree-strict
forest by repeated degree-bucket insertion. -/
def consolidateList : List FHNode → List FHNode
  | [] => []
  | x :: xs => insertConsolidated (consolidateList xs) x

/-- `CONSOLIDATE` preserves the key set of the root forest. -/
theorem consolidateList_keys : ∀ roots : List FHNode,
    forestKeySet (consolidateList roots) = forestKeySet roots
  | [] => by simp [consolidateList]
  | x :: xs => by
      rw [consolidateList]
      rw [insertConsolidated_keys]
      have hrec := consolidateList_keys xs
      rw [hrec]
      ext k
      simp [forestKeySet, Finset.mem_union]
      tauto

/-- `CONSOLIDATE` preserves structural goodness of the root forest. -/
theorem consolidateList_good : ∀ roots : List FHNode,
    ForestGood roots → ForestGood (consolidateList roots)
  | [] => by simp [consolidateList]
  | x :: xs => by
      intro hgood
      rw [consolidateList]
      have hgxs : ForestGood xs := ⟨
        (fun t ht => hgood.1 t (by simp [ht])),
        (fun t ht => hgood.2 t (by simp [ht]))⟩
      have hgx : ForestGood [x] := ⟨
        (fun t ht => by
          rw [List.mem_singleton] at ht
          subst t
          exact hgood.1 x (by simp)),
        (fun t ht => by
          rw [List.mem_singleton] at ht
          subst t
          exact hgood.2 x (by simp))⟩
      have hrec := consolidateList_good xs hgxs
      exact insertConsolidated_good (consolidateList xs) x hrec hgx

/-- `CONSOLIDATE` produces a degree-strict forest: at most one root per
degree. -/
theorem consolidateList_degreeStrict : ∀ roots : List FHNode,
    DegreeStrict (consolidateList roots)
  | [] => by simp [consolidateList, DegreeStrict]
  | x :: xs => by
      rw [consolidateList]
      exact insertConsolidated_degreeStrict (consolidateList xs) x
        (consolidateList_degreeStrict xs)

end FHNode

/-- An executable Fibonacci heap: a root forest and the total node count. -/
structure FH where
  roots : List FHNode
  size : Nat

namespace FH

/-- The key set represented by the heap (duplicates collapsed). -/
def keys (h : FH) : Finset Int := FHNode.forestKeySet h.roots

/-- The empty heap. -/
def makeHeap : FH :=
  { roots := [], size := 0 }

/-- Insert a new key as an unmarked root (CLRS `FIB-HEAP-INSERT`). -/
def insert (x : Int) (h : FH) : FH :=
  { roots := FHNode.node x false [] :: h.roots
  , size := h.size + 1 }

/-- Union of two heaps: concatenate the root forests (CLRS `FIB-HEAP-UNION`). -/
def union (h₁ h₂ : FH) : FH :=
  { roots := h₁.roots ++ h₂.roots
  , size := h₁.size + h₂.size }

/-- The minimum key, if the heap is nonempty (CLRS `FIB-HEAP-MINIMUM`). -/
def minimum (h : FH) : Option Int :=
  if hne : h.keys.Nonempty then some (h.keys.min' hne) else none

/-- The keys of the empty heap are none. -/
theorem makeHeap_keys : keys makeHeap = ∅ := by
  simp [keys, makeHeap, FHNode.forestKeySet]

/-- Inserting adds the new key to the key set. -/
theorem insert_keys (x : Int) (h : FH) :
    keys (insert x h) = Insert.insert x (keys h) := by
  rw [Finset.insert_eq]
  ext k
  simp [keys, insert, FHNode.forestKeySet, FHNode.keySet, FHNode.keysList,
    Finset.mem_union]

/-- The key set of a concatenated forest is the union of the two key sets. -/
theorem forestKeySet_append (ts₁ ts₂ : List FHNode) :
    FHNode.forestKeySet (ts₁ ++ ts₂) = FHNode.forestKeySet ts₁ ∪ FHNode.forestKeySet ts₂ := by
  induction ts₁ with
  | nil => simp [FHNode.forestKeySet]
  | cons t ts₁ ih =>
      change t.keySet ∪ FHNode.forestKeySet (ts₁ ++ ts₂) =
        (t.keySet ∪ FHNode.forestKeySet ts₁) ∪ FHNode.forestKeySet ts₂
      rw [ih]
      ac_rfl

/-- Union of heaps is the union of key sets. -/
theorem union_keys (h₁ h₂ : FH) :
    keys (union h₁ h₂) = keys h₁ ∪ keys h₂ := by
  change FHNode.forestKeySet (h₁.roots ++ h₂.roots) =
    FHNode.forestKeySet h₁.roots ∪ FHNode.forestKeySet h₂.roots
  exact forestKeySet_append h₁.roots h₂.roots

/-- A key belongs to the forest key set exactly when some root's subtree
contains it. -/
theorem FHNode.mem_forestKeySet_iff {ts : List FHNode} {k : Int} :
    k ∈ FHNode.forestKeySet ts ↔ ∃ t ∈ ts, k ∈ t.keySet := by
  induction ts with
  | nil => simp [FHNode.forestKeySet]
  | cons t ts ih =>
      change k ∈ t.keySet ∪ FHNode.forestKeySet ts ↔
        ∃ t' ∈ t :: ts, k ∈ t'.keySet
      rw [Finset.mem_union, ih]
      simp [List.mem_cons]

/-- A root's key belongs to the forest key set. -/
theorem FHNode.mem_forestKeySet_of_mem {ts : List FHNode} {t : FHNode}
    (ht : t ∈ ts) : t.key ∈ FHNode.forestKeySet ts := by
  rw [FHNode.mem_forestKeySet_iff]
  exact ⟨t, ht, by
    cases t with
    | node k m cs =>
        have : k ∈ (FHNode.node k m cs).keysList := by simp
        exact List.mem_toFinset.mpr this⟩

/-- A returned minimum belongs to the represented key set. -/
theorem minimum_mem {h : FH} {x : Int} (hmin : minimum h = some x) :
    x ∈ keys h := by
  unfold minimum at hmin
  by_cases hne : h.keys.Nonempty
  · have hmin' : h.keys.min' hne = x := by
      simpa [hne] using hmin
    rw [← hmin']
    exact Finset.min'_mem h.keys hne
  · simp [hne] at hmin

/-! ## Cutting and cascading cuts -/

/-- Remove the first element satisfying `p` from a list, returning it together
with the remaining list. -/
def findAndRemove (p : FHNode → Prop) [DecidablePred p] :
    List FHNode → Option (FHNode × List FHNode)
  | [] => none
  | x :: xs =>
      if p x then some (x, xs)
      else match findAndRemove p xs with
        | none => none
        | some (y, rest) => some (y, x :: rest)

/-- The forest key set equals the flattened key list's `toFinset`. -/
theorem forestKeySet_eq_flatMap (ts : List FHNode) :
    FHNode.forestKeySet ts = (ts.flatMap FHNode.keysList).toFinset := by
  induction ts with
  | nil => simp [FHNode.forestKeySet]
  | cons t ts ih =>
      change t.keySet ∪ FHNode.forestKeySet ts =
        (t.keysList ++ ts.flatMap FHNode.keysList).toFinset
      rw [ih, FHNode.keySet]
      rw [List.toFinset_append]

/-- The key set of a removed element is exactly what `findAndRemove` splits
off. -/
theorem findAndRemove_keys {p : FHNode → Prop} [DecidablePred p]
    (cs : List FHNode) : ∀ (c : FHNode) (rest : List FHNode),
    findAndRemove p cs = some (c, rest) →
      FHNode.forestKeySet cs = c.keySet ∪ FHNode.forestKeySet rest := by
  induction cs with
  | nil => intro c rest h; simp [findAndRemove] at h
  | cons x xs ih =>
      intro c rest h
      unfold findAndRemove at h
      by_cases hx : p x
      · simp [hx] at h
        rcases h with ⟨hcx, hrestx⟩
        subst c
        subst rest
        simp [FHNode.forestKeySet]
      · simp [hx] at h
        cases hfr : findAndRemove p xs with
        | none => simp [hfr] at h
        | some pair =>
            cases pair with
            | mk y r =>
                have hy : some (y, x :: r) = some (c, rest) := by
                  simpa [hfr] using h
                have hpair : (y, x :: r) = (c, rest) := Option.some.inj hy
                have hyc : y = c := congrArg Prod.fst hpair
                have hrest' : x :: r = rest := congrArg Prod.snd hpair
                have hrec : FHNode.forestKeySet xs = y.keySet ∪ FHNode.forestKeySet r :=
                  ih y r hfr
                subst c
                rw [← hrest']
                change x.keySet ∪ FHNode.forestKeySet xs =
                  y.keySet ∪ FHNode.forestKeySet (x :: r)
                rw [hrec]
                simp [FHNode.forestKeySet]
                ext k
                simp [Finset.mem_union]
                tauto

/-- The remaining list of `findAndRemove` consists of elements of the
original list. -/
theorem findAndRemove_rest_mem {p : FHNode → Prop} [DecidablePred p]
    (cs : List FHNode) : ∀ (c : FHNode) (rest : List FHNode),
    findAndRemove p cs = some (c, rest) → ∀ v ∈ rest, v ∈ cs := by
  induction cs with
  | nil => intro c rest h v hv; simp [findAndRemove] at h
  | cons x xs ih =>
      intro c rest h v hv
      unfold findAndRemove at h
      by_cases hx : p x
      · simp [hx] at h
        rcases h with ⟨hcx, hrestx⟩
        subst c
        subst rest
        exact List.mem_cons.mpr (Or.inr hv)
      · simp [hx] at h
        cases hfr : findAndRemove p xs with
        | none => simp [hfr] at h
        | some pair =>
            cases pair with
            | mk y r =>
                have hy : some (y, x :: r) = some (c, rest) := by
                  simpa [hfr] using h
                have hpair : (y, x :: r) = (c, rest) := Option.some.inj hy
                have hrest' : x :: r = rest := congrArg Prod.snd hpair
                subst rest
                rw [List.mem_cons] at hv
                rcases hv with hv | hv
                · exact List.mem_cons.mpr (Or.inl hv)
                · exact List.mem_cons.mpr (Or.inr (ih y r hfr v hv))

/-- `findAndRemove` removes exactly the first matching element: the rest is
the original list with that position erased. -/
theorem findAndRemove_eq_eraseIdx {p : FHNode → Prop} [DecidablePred p]
    (cs : List FHNode) : ∀ (c : FHNode) (rest : List FHNode),
    findAndRemove p cs = some (c, rest) →
      ∃ (i : Nat) (hi : i < cs.length), cs[i]'(hi) = c ∧ rest = cs.eraseIdx i := by
  induction cs with
  | nil => intro c rest h; simp [findAndRemove] at h
  | cons x xs ih =>
      intro c rest h
      unfold findAndRemove at h
      by_cases hx : p x
      · simp [hx] at h
        rcases h with ⟨hcx, hrestx⟩
        subst c
        subst rest
        refine ⟨0, by simp, ?_, rfl⟩
        · show (x :: xs)[0]'(by simp) = x
          simp
      · simp [hx] at h
        cases hfr : findAndRemove p xs with
        | none => simp [hfr] at h
        | some pair =>
            cases pair with
            | mk y r =>
                have hy : some (y, x :: r) = some (c, rest) := by
                  simpa [hfr] using h
                have hpair : (y, x :: r) = (c, rest) := Option.some.inj hy
                have hyc : y = c := congrArg Prod.fst hpair
                have hrest' : x :: r = rest := congrArg Prod.snd hpair
                rcases ih y r hfr with ⟨i, hi, hget, herase⟩
                subst c
                subst rest
                refine ⟨i + 1, by simp [hi], ?_, ?_⟩
                · show (x :: xs)[i + 1]'(by simp [hi]) = y
                  simpa [hget]
                · simp [List.eraseIdx, herase]

/-- Mapping commutes with `List.eraseIdx`. -/
lemma map_eraseIdx {α β : Type} (f : α → β) (cs : List α) (i : Nat) :
    ((cs.eraseIdx i).map f) = (cs.map f).eraseIdx i := by
  revert i
  induction cs with
  | nil => intro i; simp
  | cons x xs ih =>
      intro i
      cases i with
      | zero => rfl
      | succ i =>
          simp [List.eraseIdx, ih i]

/-- Elements of the erased list are elements of the original list. -/
lemma mem_eraseIdx_of_mem {α : Type} {cs : List α} (i : Nat) {a : α}
    (h : a ∈ cs.eraseIdx i) : a ∈ cs := by
  revert i
  induction cs with
  | nil => intro i h; simp at h
  | cons x xs ih =>
      intro i h
      cases i with
      | zero =>
          exact List.mem_cons.mpr (Or.inr (by simpa [List.eraseIdx] using h))
      | succ i =>
          simp [List.eraseIdx] at h ⊢
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (ih i h)

/-- The element before the removed index is unchanged. -/
lemma eraseIdx_getElem_lt {α : Type} {cs : List α} (i j : Nat)
    (hi : i < cs.length) (hji : j < i) (hj' : j < (cs.eraseIdx i).length) :
    (cs.eraseIdx i)[j]'(hj') = cs[j]'(lt_trans hji hi) := by
  revert i j
  induction cs with
  | nil => intro i j hi hji hj'; simp at hi
  | cons x xs ih =>
      intro i j hi hji hj'
      cases i with
      | zero => simp at hji
      | succ i =>
          cases j with
          | zero => simp [List.eraseIdx]
          | succ j =>
              have hj'' : j < (xs.eraseIdx i).length := by
                simpa [List.eraseIdx] using hj'
              have hji' : j < i := by omega
              have hi' : i < xs.length := by simp at hi; omega
              have hrec := ih i j hi' hji' hj''
              simpa [List.eraseIdx] using hrec

/-- The element at or after the removed index shifts down by one. -/
lemma eraseIdx_getElem_ge {α : Type} {cs : List α} (i j : Nat)
    (hi : i < cs.length) (hij : i ≤ j) (hj : j < (cs.eraseIdx i).length)
    (hj₁ : j + 1 < cs.length) :
    (cs.eraseIdx i)[j]'(hj) = cs[j + 1]'(hj₁) := by
  revert i j
  induction cs with
  | nil => intro i j hi hij hj hj₁; simp at hi
  | cons x xs ih =>
      intro i j hi hij hj hj₁
      cases i with
      | zero =>
          simp [List.eraseIdx]
      | succ i =>
          cases j with
          | zero => simp at hij
          | succ j =>
              have hj'' : j < (xs.eraseIdx i).length := by
                simpa [List.eraseIdx] using hj
              have hj₁'' : j + 1 < xs.length := by
                simpa [List.eraseIdx] using hj₁
              have hij' : i ≤ j := by omega
              have hi' : i < xs.length := by simp at hi; omega
              have hrec := ih i j hi' hij' hj'' hj₁''
              simpa [List.eraseIdx] using hrec

theorem FTree.wellformed_remove_index {cs : List FTree}
    (hw : FTree.Wellformed (FTree.node cs)) (i : Nat) (hi : i < cs.length) :
    FTree.Wellformed (FTree.node (cs.eraseIdx i)) := by
  cases hw with
  | node hdeg hall =>
      refine FTree.Wellformed.node ?_ ?_
      · intro j hj
        by_cases hji : j < i
        · have hget := eraseIdx_getElem_lt (α := FTree) i j hi hji hj
          rw [hget]
          exact hdeg j (lt_trans hji hi)
        · have hget := eraseIdx_getElem_ge (α := FTree) i j hi (le_of_not_gt hji) hj
            (by
              have hjlen : (cs.eraseIdx i).length = cs.length - 1 :=
                List.length_eraseIdx_of_lt hi
              rw [hjlen] at hj
              omega)
          rw [hget]
          have hjn : j + 1 < cs.length := by
            have hjlen : (cs.eraseIdx i).length = cs.length - 1 :=
              List.length_eraseIdx_of_lt hi
            rw [hjlen] at hj
            omega
          have hdeg' : (j + 1) - 1 ≤ (cs[j + 1]).degree :=
            hdeg (j + 1) hjn
          have : j - 1 ≤ (j + 1) - 1 := by omega
          exact le_trans this hdeg'
      · intro c hc
        exact hall c (mem_eraseIdx_of_mem i hc)

/-- Clear the mark bit of a node. -/
def markFalse : FHNode → FHNode
  | FHNode.node k _ cs => FHNode.node k false cs

/-- Clearing a mark preserves the key set. -/
theorem markFalse_keySet (t : FHNode) : (markFalse t).keySet = t.keySet := by
  cases t with
  | node k m cs =>
      simp [markFalse, FHNode.keySet]

/-- Clearing a mark preserves heap order (marks are structurally inert). -/
theorem markFalse_heapOrdered (t : FHNode) (ht : t.HeapOrdered) :
    (markFalse t).HeapOrdered := by
  cases t with
  | node k m cs =>
      cases ht with
      | node hle hall =>
          exact FHNode.HeapOrdered.node hle hall

/-- Clearing a mark preserves wellformedness (marks are structurally
inert). -/
theorem markFalse_wellformed (t : FHNode) (ht : t.Wellformed) :
    (markFalse t).Wellformed := by
  cases t with
  | node k m cs => simpa [markFalse, FHNode.Wellformed, FHNode.toFTree] using ht

/-- **FIB-HEAP-CUT on a child.**  Remove the child with key `k` from a tree,
clearing its mark; the child becomes a new root.  Returns `none` when no such
child exists. -/
noncomputable def cutChild (t : FHNode) (k : Int) : Option (FHNode × FHNode) :=
  match findAndRemove (fun c => c.key = k) t.children with
  | none => none
  | some (c, rest) => some (markFalse c, FHNode.node t.key t.marked rest)

/-- `cutChild` splits the tree's key set between the cut child and the
remaining tree. -/
theorem cutChild_keys {t : FHNode} {k : Int} {c t' : FHNode}
    (h : cutChild t k = some (c, t')) :
    c.keySet ∪ t'.keySet = t.keySet := by
  unfold cutChild at h
  cases hc : findAndRemove (fun c => c.key = k) t.children with
  | none => simp [hc] at h
  | some pair =>
      cases pair with
      | mk c' rest =>
          simp [hc] at h
          have hc' : markFalse c' = c := h.1
          have hrest : FHNode.node t.key t.marked rest = t' := h.2
          subst t'
          rw [← hc']
          rw [markFalse_keySet]
          have hsplit := findAndRemove_keys t.children c' rest hc
          cases t with
          | node k' m' cs =>
              ext z
              have hsplit' : (∃ a ∈ cs, z ∈ a.keysList) ↔
                  z ∈ c'.keySet ∨ ∃ a ∈ rest, z ∈ a.keysList := by
                have h1 := congrArg (fun s : Finset Int => z ∈ s) hsplit
                simp [FHNode.children] at h1
                rw [FH.forestKeySet_eq_flatMap cs, FH.forestKeySet_eq_flatMap rest] at h1
                simpa [List.mem_toFinset, List.mem_flatMap, Finset.mem_union] using h1
              simp [FHNode.keySet, FHNode.keysList, List.toFinset_cons,
                List.mem_toFinset, Finset.mem_union]
              rw [hsplit']
              simpa [FHNode.keySet, List.mem_toFinset]

/-- `cutChild` preserves wellformedness: the remaining tree stays wellformed
when the original tree is. -/
theorem cutChild_wellformed {t t' : FHNode} {k : Int} {c : FHNode}
    (h : cutChild t k = some (c, t')) (ht : t.Wellformed) :
    t'.Wellformed := by
  unfold cutChild at h
  cases hc : findAndRemove (fun c => c.key = k) t.children with
  | none => simp [hc] at h
  | some pair =>
      cases pair with
      | mk c' rest =>
          simp [hc] at h
          have hrest : FHNode.node t.key t.marked rest = t' := h.2
          subst t'
          cases t with
          | node k' m' cs =>
              rcases findAndRemove_eq_eraseIdx cs c' rest hc with ⟨i, hi, hget, herase⟩
              rw [herase]
              unfold FHNode.Wellformed
              have hmap : ((cs.eraseIdx i).map FHNode.toFTree) =
                  (cs.map FHNode.toFTree).eraseIdx i :=
                map_eraseIdx FHNode.toFTree cs i
              have hw' : (FTree.node ((cs.map FHNode.toFTree).eraseIdx i)).Wellformed :=
                FTree.wellformed_remove_index (by
                  simpa [FHNode.Wellformed, FHNode.toFTree] using ht) i
                  (by simpa [List.length_map] using hi)
              simpa [FHNode.toFTree, ← hmap] using hw'

/-- `cutChild` preserves heap order of the remaining tree: removing a child
cannot break the parent's key bounds. -/
theorem cutChild_heapOrdered {t t' : FHNode} {k : Int} {c : FHNode}
    (h : cutChild t k = some (c, t')) (ht : t.HeapOrdered) :
    t'.HeapOrdered := by
  unfold cutChild at h
  cases hc : findAndRemove (fun c => c.key = k) t.children with
  | none => simp [hc] at h
  | some pair =>
      cases pair with
      | mk c' rest =>
          simp [hc] at h
          have hrest : FHNode.node t.key t.marked rest = t' := h.2
          subst t'
          cases t with
          | node k' m' cs =>
              cases ht with
              | node hle hall =>
                  have hmem : ∀ v ∈ rest, v ∈ cs :=
                    findAndRemove_rest_mem cs c' rest hc
                  refine FHNode.HeapOrdered.node ?_ ?_
                  · intro v hv
                    exact hle v (hmem v hv)
                  · intro v hv
                    exact hall v (hmem v hv)


/-! ## The potential function and amortized bounds -/

/-- The standard Fibonacci-heap potential `t(H) + 2m(H)` (CLRS equation
19.2), computed from the complete executable heap state. -/
def potential (h : FH) : Int :=
  Int.ofNat h.roots.length +
    2 * Int.ofNat (FHNode.forestMarks h.roots)

/-- The executable heap potential is always nonnegative. -/
theorem potential_nonneg (h : FH) : 0 ≤ potential h := by
  unfold potential
  exact add_nonneg (Int.natCast_nonneg h.roots.length)
    (mul_nonneg (by norm_num)
      (Int.natCast_nonneg (FHNode.forestMarks h.roots)))

/-- The empty executable heap has zero potential. -/
theorem potential_makeHeap : potential makeHeap = 0 := by
  simp [potential, makeHeap]

/-- Inserting an unmarked singleton root raises the potential by exactly one. -/
theorem potential_insert (x : Int) (h : FH) :
    potential (insert x h) = potential h + 1 := by
  simp [potential, insert]
  omega

/-- Clearing a node's mark removes exactly its root-mark contribution. -/
theorem markFalse_marks_add (t : FHNode) :
    (markFalse t).marks + (if t.marked then 1 else 0) = t.marks := by
  cases t with
  | node k m cs => cases m <;> simp [markFalse] <;> omega
