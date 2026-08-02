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
- `FHNode.consolidateList_keys`, `consolidateList_good`, and
  `consolidateList_degreeStrict`: `CONSOLIDATE` correctness and at most one
  root per degree after
  consolidation
- `FH`: an executable heap (root forest + node count)
- `FH.makeHeap` / `FH.insert` / `FH.union` / `FH.minimum`:
  executable operations with key-set specifications
- `FH.cutChildAt` / `FH.cutRootChildAt`: index-addressed direct-child CUT,
  lifted to a complete heap state with key-set and invariant preservation
- `FH.potential` / `FH.cutRootChildAt_potential_eq`: executable
  `t(H) + 2m(H)` accounting and the exact one-step CUT potential change

Current gaps:

- A global executable `FH.Valid`/`FH.Represents` bridge, an `extractMin` that
  invokes `consolidateList`, arbitrary-node handles or paths, cascading cuts,
  executable `decreaseKey`/`delete`, and actual-operation cost semantics remain
  future targets.  Circular pointer lists are a lower-level refinement of the
  persistent root-list model used here.
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

/-- The keys of one subtree with multiplicity. -/
def keyBag (t : FHNode) : Multiset Int :=
  ↑t.keysList

/-- The keys of a root forest with multiplicity. -/
def forestKeyBag (roots : List FHNode) : Multiset Int :=
  ↑(roots.flatMap FHNode.keysList)

/-- The actual number of nodes represented by a root forest. -/
def forestSize (roots : List FHNode) : Nat :=
  (roots.map FHNode.size).sum

/-- Every root has the CLRS root mark `false`. -/
def RootsUnmarked (roots : List FHNode) : Prop :=
  ∀ root ∈ roots, root.marked = false

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
      (if m then 1 else 0) + (cs.map marks).sum := by
  rw [marks]

@[simp] theorem forestMarks_nil : forestMarks [] = 0 := rfl

@[simp] theorem forestMarks_cons (t : FHNode) (ts : List FHNode) :
    forestMarks (t :: ts) = t.marks + forestMarks ts := by
  simp [forestMarks]

@[simp] theorem keyBag_node (k : Int) (m : Bool) (cs : List FHNode) :
    keyBag (node k m cs) = {k} + forestKeyBag cs := by
  simp [keyBag, forestKeyBag]

@[simp] theorem forestKeyBag_nil : forestKeyBag [] = 0 := rfl

@[simp] theorem forestKeyBag_cons (t : FHNode) (ts : List FHNode) :
    forestKeyBag (t :: ts) = t.keyBag + forestKeyBag ts := by
  simp [forestKeyBag, keyBag]

/-- Forest-bag membership identifies a containing root subtree. -/
theorem mem_forestKeyBag_iff {roots : List FHNode} {y : Int} :
    y ∈ forestKeyBag roots ↔ ∃ root ∈ roots, y ∈ root.keyBag := by
  simp [forestKeyBag, keyBag, List.mem_flatMap]

theorem forestKeyBag_append (xs ys : List FHNode) :
    forestKeyBag (xs ++ ys) = forestKeyBag xs + forestKeyBag ys := by
  simp [forestKeyBag, List.flatMap_append]

@[simp] theorem forestSize_nil : forestSize [] = 0 := rfl

@[simp] theorem forestSize_cons (t : FHNode) (ts : List FHNode) :
    forestSize (t :: ts) = t.size + forestSize ts := by
  simp [forestSize]

theorem forestSize_append (xs ys : List FHNode) :
    forestSize (xs ++ ys) = forestSize xs + forestSize ys := by
  simp [forestSize, List.sum_append]

theorem size_eq_one_add_forestSize (t : FHNode) :
    t.size = 1 + forestSize t.children := by
  cases t
  simp [forestSize]

theorem forestKeySet_cons (t : FHNode) (ts : List FHNode) :
    forestKeySet (t :: ts) = t.keySet ∪ forestKeySet ts := by
  simp [forestKeySet]

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

/-- `LINK` preserves the exact key multiset of both subtrees. -/
theorem link_keyBag (x y : FHNode) :
    (link x y).keyBag = x.keyBag + y.keyBag := by
  unfold link
  by_cases h : x.key ≤ y.key
  · cases x with
    | node k m cs =>
        have h' : k ≤ y.key := by simpa using h
        simp only [key_node, marked_node, children_node]
        rw [if_pos h']
        simp [forestKeyBag_append, add_assoc]
  · cases y with
    | node k m cs =>
        have h' : ¬x.key ≤ k := by simpa using h
        simp only [key_node, marked_node, children_node]
        rw [if_neg h']
        simp [forestKeyBag_append]
        ac_rfl

/-- Linking two unmarked roots leaves the resulting root unmarked. -/
theorem link_marked_false (x y : FHNode)
    (hx : x.marked = false) (hy : y.marked = false) :
    (link x y).marked = false := by
  unfold link
  by_cases h : x.key ≤ y.key
  · rw [if_pos h]
    exact hx
  · rw [if_neg h]
    exact hy

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

/-- One bucket insertion preserves the exact key multiset. -/
theorem insertConsolidated_keyBag (ys : List FHNode) (x : FHNode) :
    forestKeyBag (insertConsolidated ys x) = forestKeyBag ys + x.keyBag := by
  revert x
  induction ys with
  | nil => intro x; simp [insertConsolidated]
  | cons y ys ih =>
      intro x
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · rw [if_pos h1, ih, link_keyBag]
        simp only [forestKeyBag_cons]
        ac_rfl
      · rw [if_neg h1]
        by_cases h2 : y.degree < x.degree
        · rw [if_pos h2, forestKeyBag_cons, ih, forestKeyBag_cons]
          ac_rfl
        · rw [if_neg h2]
          simp only [forestKeyBag_cons]
          ac_rfl

/-- One bucket insertion preserves the actual number of represented nodes. -/
theorem insertConsolidated_forestSize (ys : List FHNode) (x : FHNode) :
    forestSize (insertConsolidated ys x) = forestSize ys + x.size := by
  revert x
  induction ys with
  | nil => intro x; simp [insertConsolidated]
  | cons y ys ih =>
      intro x
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · rw [if_pos h1, ih, link_size]
        simp only [forestSize_cons]
        omega
      · rw [if_neg h1]
        by_cases h2 : y.degree < x.degree
        · rw [if_pos h2, forestSize_cons, ih, forestSize_cons]
          omega
        · rw [if_neg h2]
          simp only [forestSize_cons]
          omega

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

/-- Bucket insertion preserves the CLRS rule that every root is unmarked. -/
theorem insertConsolidated_rootsUnmarked (ys : List FHNode) (x : FHNode)
    (hys : RootsUnmarked ys) (hx : x.marked = false) :
    RootsUnmarked (insertConsolidated ys x) := by
  revert x
  induction ys with
  | nil =>
      intro x hx
      intro t ht
      change t ∈ [x] at ht
      rw [List.mem_singleton] at ht
      subst t
      exact hx
  | cons y ys ih =>
      intro x hx
      have hy : y.marked = false := hys y (by simp)
      have hys' : RootsUnmarked ys := by
        intro t ht
        exact hys t (by simp [ht])
      unfold insertConsolidated
      by_cases h1 : y.degree = x.degree
      · rw [if_pos h1]
        exact ih hys' (link x y) (link_marked_false x y hx hy)
      · rw [if_neg h1]
        by_cases h2 : y.degree < x.degree
        · rw [if_pos h2]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with ht | ht
          · subst t
            exact hy
          · exact ih hys' x hx t ht
        · rw [if_neg h2]
          intro t ht
          rw [List.mem_cons] at ht
          rcases ht with ht | ht
          · subst t
            exact hx
          · rw [List.mem_cons] at ht
            rcases ht with ht | ht
            · subst t
              exact hy
            · exact hys' t ht

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

/-- `CONSOLIDATE` preserves the exact forest key multiset. -/
theorem consolidateList_keyBag : ∀ roots : List FHNode,
    forestKeyBag (consolidateList roots) = forestKeyBag roots
  | [] => by simp [consolidateList]
  | x :: xs => by
      rw [consolidateList, insertConsolidated_keyBag,
        consolidateList_keyBag, forestKeyBag_cons]
      ac_rfl

/-- `CONSOLIDATE` preserves the actual number of represented nodes. -/
theorem consolidateList_forestSize : ∀ roots : List FHNode,
    forestSize (consolidateList roots) = forestSize roots
  | [] => by simp [consolidateList]
  | x :: xs => by
      rw [consolidateList, insertConsolidated_forestSize,
        consolidateList_forestSize, forestSize_cons]
      omega

/-- `CONSOLIDATE` preserves the CLRS root-mark rule. -/
theorem consolidateList_rootsUnmarked : ∀ roots : List FHNode,
    RootsUnmarked roots → RootsUnmarked (consolidateList roots)
  | [] => by simp [consolidateList, RootsUnmarked]
  | x :: xs => by
      intro hunmarked
      rw [consolidateList]
      have hx : x.marked = false := hunmarked x (by simp)
      have hxs : RootsUnmarked xs := by
        intro t ht
        exact hunmarked t (by simp [ht])
      exact insertConsolidated_rootsUnmarked (consolidateList xs) x
        (consolidateList_rootsUnmarked xs hxs) hx

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

/-- The executable heap's exact key multiset. -/
def keyBag (h : FH) : Multiset Int :=
  FHNode.forestKeyBag h.roots

/-- Exact multiset representation for the executable heap. -/
def Represents (h : FH) (bag : Multiset Int) : Prop :=
  h.keyBag = bag

/-- Structural, root-mark, and stored-size validity. -/
def Valid (h : FH) : Prop :=
  FHNode.ForestGood h.roots ∧
  FHNode.RootsUnmarked h.roots ∧
  h.size = FHNode.forestSize h.roots

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

/-- The empty executable heap is valid. -/
theorem makeHeap_valid : makeHeap.Valid := by
  simp [Valid, makeHeap, FHNode.ForestGood, FHNode.RootsUnmarked]

/-- Inserting an unmarked singleton root preserves executable validity. -/
theorem insert_valid (x : Int) (h : FH) (hvalid : h.Valid) :
    (insert x h).Valid := by
  rcases hvalid with ⟨⟨hordered, hwellformed⟩, hunmarked, hsize⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro t ht
      change t ∈ FHNode.node x false [] :: h.roots at ht
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst t
        exact FHNode.leaf_heapOrdered x
      · exact hordered t ht
    · intro t ht
      change t ∈ FHNode.node x false [] :: h.roots at ht
      rw [List.mem_cons] at ht
      rcases ht with ht | ht
      · subst t
        exact FHNode.leaf_wellformed x
      · exact hwellformed t ht
  · intro t ht
    change t ∈ FHNode.node x false [] :: h.roots at ht
    rw [List.mem_cons] at ht
    rcases ht with ht | ht
    · subst t
      rfl
    · exact hunmarked t ht
  · change h.size + 1 = FHNode.forestSize (FHNode.node x false [] :: h.roots)
    rw [FHNode.forestSize_cons, hsize]
    simp
    omega

/-- Concatenating two valid root forests preserves executable validity. -/
theorem union_valid (h₁ h₂ : FH)
    (hvalid₁ : h₁.Valid) (hvalid₂ : h₂.Valid) :
    (union h₁ h₂).Valid := by
  rcases hvalid₁ with ⟨⟨hordered₁, hwellformed₁⟩, hunmarked₁, hsize₁⟩
  rcases hvalid₂ with ⟨⟨hordered₂, hwellformed₂⟩, hunmarked₂, hsize₂⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro t ht
      change t ∈ h₁.roots ++ h₂.roots at ht
      rw [List.mem_append] at ht
      exact ht.elim (hordered₁ t) (hordered₂ t)
    · intro t ht
      change t ∈ h₁.roots ++ h₂.roots at ht
      rw [List.mem_append] at ht
      exact ht.elim (hwellformed₁ t) (hwellformed₂ t)
  · intro t ht
    change t ∈ h₁.roots ++ h₂.roots at ht
    rw [List.mem_append] at ht
    exact ht.elim (hunmarked₁ t) (hunmarked₂ t)
  · change h₁.size + h₂.size = FHNode.forestSize (h₁.roots ++ h₂.roots)
    rw [FHNode.forestSize_append, hsize₁, hsize₂]

/-- The minimum key, if the heap is nonempty (CLRS `FIB-HEAP-MINIMUM`). -/
def minimum (h : FH) : Option Int :=
  if hne : h.keys.Nonempty then some (h.keys.min' hne) else none

/-- Remove the leftmost minimum-key root, returning it and the remaining
roots in their original relative order. -/
def removeMinRoot : List FHNode → Option (FHNode × List FHNode)
  | [] => none
  | x :: xs =>
      match removeMinRoot xs with
      | none => some (x, [])
      | some (y, rest) =>
          if x.key ≤ y.key then some (x, xs)
          else some (y, x :: rest)

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

/-- Minimum-root removal fails exactly on the empty root forest. -/
theorem removeMinRoot_none_iff (roots : List FHNode) :
    removeMinRoot roots = none ↔ roots = [] := by
  cases roots with
  | nil => simp [removeMinRoot]
  | cons x xs =>
      cases hrec : removeMinRoot xs with
      | none => simp [removeMinRoot, hrec]
      | some pair =>
          rcases pair with ⟨y, rest⟩
          by_cases hxy : x.key ≤ y.key <;> simp [removeMinRoot, hrec, hxy]

/-- Successful minimum-root removal returns a permutation decomposition of
the original root forest. -/
theorem removeMinRoot_perm {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    (z :: rest).Perm roots := by
  induction roots generalizing z rest with
  | nil => simp [removeMinRoot] at hremove
  | cons x xs ih =>
      rw [removeMinRoot] at hremove
      cases hrec : removeMinRoot xs with
      | none =>
          simp only [hrec] at hremove
          simp only [Option.some.injEq, Prod.mk.injEq] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          have hxs : xs = [] := (removeMinRoot_none_iff xs).mp hrec
          subst xs
          exact List.Perm.refl [x]
      | some pair =>
          rcases pair with ⟨y, r⟩
          simp only [hrec] at hremove
          by_cases hxy : x.key ≤ y.key
          · rw [if_pos hxy] at hremove
            simp only [Option.some.injEq, Prod.mk.injEq] at hremove
            rcases hremove with ⟨rfl, rfl⟩
            exact List.Perm.refl (x :: xs)
          · rw [if_neg hxy] at hremove
            simp only [Option.some.injEq, Prod.mk.injEq] at hremove
            rcases hremove with ⟨rfl, rfl⟩
            exact (List.Perm.swap x y r).trans ((ih hrec).cons x)

/-- Minimum-root removal splits the exact forest key bag. -/
theorem removeMinRoot_keyBag {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    FHNode.forestKeyBag roots = z.keyBag + FHNode.forestKeyBag rest := by
  rw [← FHNode.forestKeyBag_cons]
  unfold FHNode.forestKeyBag
  apply Multiset.coe_eq_coe.mpr
  exact (removeMinRoot_perm hremove).flatMap
    (fun t _ => List.Perm.refl t.keysList) |>.symm

/-- Minimum-root removal splits the actual forest node count. -/
theorem removeMinRoot_forestSize {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    FHNode.forestSize roots = z.size + FHNode.forestSize rest := by
  rw [← FHNode.forestSize_cons]
  exact ((removeMinRoot_perm hremove).map FHNode.size).sum_eq.symm

/-- Structural goodness projects to the selected root and remaining forest. -/
theorem removeMinRoot_good {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hgood : FHNode.ForestGood roots) :
    z.HeapOrdered ∧ z.Wellformed ∧ FHNode.ForestGood rest := by
  have hperm := removeMinRoot_perm hremove
  have hz : z ∈ roots := hperm.mem_iff.mp (by simp)
  refine ⟨hgood.1 z hz, hgood.2 z hz, ?_⟩
  constructor
  · intro t ht
    exact hgood.1 t (hperm.mem_iff.mp (by simp [ht]))
  · intro t ht
    exact hgood.2 t (hperm.mem_iff.mp (by simp [ht]))

/-- The selected root and every remaining root inherit the root-mark rule. -/
theorem removeMinRoot_rootsUnmarked {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hunmarked : FHNode.RootsUnmarked roots) :
    z.marked = false ∧ FHNode.RootsUnmarked rest := by
  have hperm := removeMinRoot_perm hremove
  have hz : z ∈ roots := hperm.mem_iff.mp (by simp)
  refine ⟨hunmarked z hz, ?_⟩
  intro t ht
  exact hunmarked t (hperm.mem_iff.mp (by simp [ht]))

/-- The selected root has a key no greater than any original root key. -/
theorem removeMinRoot_min {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest)) :
    ∀ root ∈ roots, z.key ≤ root.key := by
  induction roots generalizing z rest with
  | nil => simp [removeMinRoot] at hremove
  | cons x xs ih =>
      rw [removeMinRoot] at hremove
      cases hrec : removeMinRoot xs with
      | none =>
          simp only [hrec] at hremove
          simp only [Option.some.injEq, Prod.mk.injEq] at hremove
          rcases hremove with ⟨rfl, rfl⟩
          have hxs : xs = [] := (removeMinRoot_none_iff xs).mp hrec
          subst xs
          simp
      | some pair =>
          rcases pair with ⟨y, r⟩
          simp only [hrec] at hremove
          by_cases hxy : x.key ≤ y.key
          · rw [if_pos hxy] at hremove
            simp only [Option.some.injEq, Prod.mk.injEq] at hremove
            rcases hremove with ⟨rfl, rfl⟩
            intro root hroot
            rw [List.mem_cons] at hroot
            rcases hroot with rfl | hroot
            · exact le_rfl
            · exact le_trans hxy (ih hrec root hroot)
          · rw [if_neg hxy] at hremove
            simp only [Option.some.injEq, Prod.mk.injEq] at hremove
            rcases hremove with ⟨rfl, rfl⟩
            intro root hroot
            rw [List.mem_cons] at hroot
            rcases hroot with rfl | hroot
            · exact le_of_not_ge hxy
            · exact ih hrec root hroot

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

/-- The duplicate-collapsing key set is the support of the exact key bag. -/
theorem keys_eq_keyBag_toFinset (h : FH) :
    h.keys = h.keyBag.toFinset := by
  rw [keys, forestKeySet_eq_flatMap]
  rfl

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

/-- Clearing a mark preserves the exact subtree key multiset. -/
theorem markFalse_keyBag (t : FHNode) :
    (markFalse t).keyBag = t.keyBag := by
  cases t
  simp [markFalse]

/-- Clearing a mark preserves subtree size. -/
theorem markFalse_size (t : FHNode) :
    (markFalse t).size = t.size := by
  cases t
  simp [markFalse]

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

/-- The children of a structurally good root form a structurally good forest. -/
theorem children_forestGood (t : FHNode)
    (hordered : t.HeapOrdered) (hwellformed : t.Wellformed) :
    FHNode.ForestGood t.children := by
  cases t with
  | node k m cs =>
      cases hordered with
      | node hle hall =>
          constructor
          · exact hall
          · have htree : (FTree.node (cs.map FHNode.toFTree)).Wellformed := by
              simpa [FHNode.Wellformed, FHNode.toFTree] using hwellformed
            cases htree with
            | node hdeg hchildren =>
                intro c hc
                have hcTree : c.toFTree.Wellformed :=
                  hchildren c.toFTree (List.mem_map.mpr ⟨c, hc, rfl⟩)
                simpa [FHNode.Wellformed] using hcTree

/-- Clearing every root mark preserves structural goodness. -/
theorem map_markFalse_forestGood (roots : List FHNode)
    (hgood : FHNode.ForestGood roots) :
    FHNode.ForestGood (roots.map markFalse) := by
  constructor
  · intro t ht
    obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp ht
    exact markFalse_heapOrdered root (hgood.1 root hroot)
  · intro t ht
    obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp ht
    exact markFalse_wellformed root (hgood.2 root hroot)

/-- Clearing root marks establishes the CLRS root-mark rule. -/
theorem map_markFalse_rootsUnmarked (roots : List FHNode) :
    FHNode.RootsUnmarked (roots.map markFalse) := by
  intro t ht
  obtain ⟨root, hroot, rfl⟩ := List.mem_map.mp ht
  cases root
  rfl

/-- Clearing every root mark preserves the exact forest key multiset. -/
theorem map_markFalse_forestKeyBag (roots : List FHNode) :
    FHNode.forestKeyBag (roots.map markFalse) =
      FHNode.forestKeyBag roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      simp only [List.map_cons, FHNode.forestKeyBag_cons,
        markFalse_keyBag, ih]

/-- Clearing every root mark preserves the actual forest node count. -/
theorem map_markFalse_forestSize (roots : List FHNode) :
    FHNode.forestSize (roots.map markFalse) =
      FHNode.forestSize roots := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      simp only [List.map_cons, FHNode.forestSize_cons, markFalse_size, ih]

/-- A heap-ordered root key is no greater than every key in its subtree. -/
theorem FHNode.heapOrdered_key_le_of_mem_keyBag {t : FHNode} {y : Int}
    (hordered : t.HeapOrdered) (hy : y ∈ t.keyBag) :
    t.key ≤ y := by
  induction hordered with
  | node hle hall ih =>
      rw [FHNode.keyBag_node, Multiset.mem_add] at hy
      rcases hy with hy | hy
      · exact le_of_eq (Multiset.mem_singleton.mp hy).symm
      · obtain ⟨child, hchild, hyChild⟩ :=
          FHNode.mem_forestKeyBag_iff.mp hy
        exact le_trans (hle child hchild) (ih child hchild hyChild)

/-- The selected minimum root is no greater than every key in the complete
original forest, not merely the other root keys. -/
theorem removeMinRoot_min_key {roots : List FHNode} {z : FHNode}
    {rest : List FHNode}
    (hremove : removeMinRoot roots = some (z, rest))
    (hgood : FHNode.ForestGood roots) :
    ∀ y ∈ FHNode.forestKeyBag roots, z.key ≤ y := by
  intro y hy
  obtain ⟨root, hroot, hyRoot⟩ := FHNode.mem_forestKeyBag_iff.mp hy
  exact le_trans (removeMinRoot_min hremove root hroot)
    (FHNode.heapOrdered_key_le_of_mem_keyBag (hgood.1 root hroot) hyRoot)

/-- Executable CLRS `FIB-HEAP-EXTRACT-MIN`: remove a minimum root, promote
and unmark its children, then consolidate equal-degree roots. -/
def extractMin (h : FH) : Option (Int × FH) :=
  match removeMinRoot h.roots with
  | none => none
  | some (z, rest) =>
      let promoted := z.children.map markFalse
      let roots' := FHNode.consolidateList (promoted ++ rest)
      some
        (z.key,
          { roots := roots'
          , size := h.size - 1 })

/-- A successful executable extract-min returns a global minimum, removes
exactly one occurrence, preserves heap validity, and leaves distinct root
degrees after consolidation. -/
theorem extractMin_correct {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    x ∈ h.keyBag ∧
    (∀ y ∈ h.keyBag, x ≤ y) ∧
    h'.keyBag = h.keyBag.erase x ∧
    h'.Valid ∧
    FHNode.DegreeStrict h'.roots := by
  rcases hvalid with ⟨hgood, hunmarked, hsize⟩
  cases hremove : removeMinRoot h.roots with
  | none => simp [extractMin, hremove] at hextract
  | some pair =>
      rcases pair with ⟨z, rest⟩
      let promoted := z.children.map markFalse
      let roots' := FHNode.consolidateList (promoted ++ rest)
      have hpair :
          (z.key, { roots := roots', size := h.size - 1 }) = (x, h') := by
        simpa [extractMin, hremove, promoted, roots'] using hextract
      have hx : z.key = x := congrArg Prod.fst hpair
      have hh : ({ roots := roots', size := h.size - 1 } : FH) = h' :=
        congrArg Prod.snd hpair
      subst x
      subst h'
      have hselected := removeMinRoot_good hremove hgood
      have hsplitBag :
          h.keyBag = z.keyBag + FHNode.forestKeyBag rest := by
        simpa [keyBag] using removeMinRoot_keyBag hremove
      have hzSelf : z.key ∈ z.keyBag := by
        cases z
        simp [FHNode.keyBag]
      have hzMem : z.key ∈ h.keyBag := by
        rw [hsplitBag, Multiset.mem_add]
        exact Or.inl hzSelf
      have hzMin : ∀ y ∈ h.keyBag, z.key ≤ y := by
        simpa [keyBag] using removeMinRoot_min_key hremove hgood
      have hnewBag :
          FHNode.forestKeyBag roots' =
            FHNode.forestKeyBag z.children + FHNode.forestKeyBag rest := by
        dsimp [roots', promoted]
        rw [FHNode.consolidateList_keyBag,
          FHNode.forestKeyBag_append, map_markFalse_forestKeyBag]
      have hzBag :
          z.keyBag = {z.key} + FHNode.forestKeyBag z.children := by
        cases z
        simp
      have holdCons :
          h.keyBag = {z.key} + FHNode.forestKeyBag roots' := by
        rw [hsplitBag, hzBag, hnewBag]
        ac_rfl
      have hbagErase :
          FHNode.forestKeyBag roots' = h.keyBag.erase z.key := by
        rw [holdCons, Multiset.singleton_add, Multiset.erase_cons_head]
      have hpromotedGood : FHNode.ForestGood promoted :=
        map_markFalse_forestGood z.children
          (children_forestGood z hselected.1 hselected.2.1)
      have happendGood : FHNode.ForestGood (promoted ++ rest) := by
        constructor
        · intro t ht
          rw [List.mem_append] at ht
          exact ht.elim (hpromotedGood.1 t) (hselected.2.2.1 t)
        · intro t ht
          rw [List.mem_append] at ht
          exact ht.elim (hpromotedGood.2 t) (hselected.2.2.2 t)
      have hrootsGood : FHNode.ForestGood roots' := by
        dsimp [roots']
        exact FHNode.consolidateList_good (promoted ++ rest) happendGood
      have hrestUnmarked : FHNode.RootsUnmarked rest :=
        (removeMinRoot_rootsUnmarked hremove hunmarked).2
      have hpromotedUnmarked : FHNode.RootsUnmarked promoted :=
        map_markFalse_rootsUnmarked z.children
      have happendUnmarked : FHNode.RootsUnmarked (promoted ++ rest) := by
        intro t ht
        rw [List.mem_append] at ht
        exact ht.elim (hpromotedUnmarked t) (hrestUnmarked t)
      have hrootsUnmarked : FHNode.RootsUnmarked roots' := by
        dsimp [roots']
        exact FHNode.consolidateList_rootsUnmarked (promoted ++ rest)
          happendUnmarked
      have hsplitSize :
          h.size = z.size + FHNode.forestSize rest := by
        calc
          h.size = FHNode.forestSize h.roots := hsize
          _ = z.size + FHNode.forestSize rest :=
            removeMinRoot_forestSize hremove
      have hnodeSize : z.size = 1 + FHNode.forestSize z.children :=
        FHNode.size_eq_one_add_forestSize z
      have hnewSize :
          FHNode.forestSize roots' =
            FHNode.forestSize z.children + FHNode.forestSize rest := by
        dsimp [roots', promoted]
        rw [FHNode.consolidateList_forestSize,
          FHNode.forestSize_append, map_markFalse_forestSize]
      have hstoredSize : h.size - 1 = FHNode.forestSize roots' := by
        omega
      refine ⟨hzMem, hzMin, ?_, ?_, ?_⟩
      · exact hbagErase
      · exact ⟨hrootsGood, hrootsUnmarked, hstoredSize⟩
      · dsimp [roots']
        exact FHNode.consolidateList_degreeStrict (promoted ++ rest)

/-- Direct exact-bag projection of executable extract-min correctness. -/
theorem extractMin_keyBag {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.keyBag = h.keyBag.erase x :=
  (extractMin_correct hvalid hextract).2.2.1

/-- Direct validity projection of executable extract-min correctness. -/
theorem extractMin_valid {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.Valid :=
  (extractMin_correct hvalid hextract).2.2.2.1

/-- Direct root-degree uniqueness projection after executable extract-min. -/
theorem extractMin_degreeStrict {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    FHNode.DegreeStrict h'.roots :=
  (extractMin_correct hvalid hextract).2.2.2.2

/-- A successful executable extract-min decreases the stored node count by
exactly one. -/
theorem extractMin_size {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h'.size + 1 = h.size := by
  rcases hvalid with ⟨hgood, hunmarked, hsize⟩
  cases hremove : removeMinRoot h.roots with
  | none => simp [extractMin, hremove] at hextract
  | some pair =>
      rcases pair with ⟨z, rest⟩
      have hpair :
          (z.key,
            { roots := FHNode.consolidateList
                (z.children.map markFalse ++ rest)
            , size := h.size - 1 }) = (x, h') := by
        simpa [extractMin, hremove] using hextract
      have hstored := congrArg (fun result : Int × FH => result.2.size) hpair
      change h.size - 1 = h'.size at hstored
      have hsplit :
          h.size = z.size + FHNode.forestSize rest := by
        calc
          h.size = FHNode.forestSize h.roots := hsize
          _ = z.size + FHNode.forestSize rest :=
            removeMinRoot_forestSize hremove
      have hzpos : 0 < z.size := by
        cases z
        simp [FHNode.size]
      omega

/-- The executable transition agrees with the existing key-set `minimum`
query. -/
theorem extractMin_minimum {h h' : FH} {x : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h')) :
    h.minimum = some x := by
  have hcorrect := extractMin_correct hvalid hextract
  have hx : x ∈ h.keys := by
    rw [keys_eq_keyBag_toFinset]
    simpa using hcorrect.1
  have hnonempty : h.keys.Nonempty := ⟨x, hx⟩
  unfold minimum
  simp only [dif_pos hnonempty, Option.some.injEq]
  apply (Finset.min'_eq_iff h.keys hnonempty x).2
  refine ⟨hx, ?_⟩
  intro y hy
  apply hcorrect.2.1 y
  rw [keys_eq_keyBag_toFinset] at hy
  simpa using hy

/-- Extracting one occurrence does not change membership of a different key. -/
theorem extractMin_mem_iff_of_ne {h h' : FH} {x y : Int}
    (hvalid : h.Valid)
    (hextract : extractMin h = some (x, h'))
    (hyx : y ≠ x) :
    y ∈ h'.keys ↔ y ∈ h.keys := by
  rw [keys_eq_keyBag_toFinset, keys_eq_keyBag_toFinset]
  simp only [Multiset.mem_toFinset]
  rw [extractMin_keyBag hvalid hextract]
  exact Multiset.mem_erase_of_ne hyx

/-- The actual forest size is zero exactly for the empty forest. -/
theorem FHNode.forestSize_eq_zero_iff (roots : List FHNode) :
    FHNode.forestSize roots = 0 ↔ roots = [] := by
  cases roots with
  | nil => simp
  | cons root roots =>
      have hroot : 0 < root.size := by
        cases root
        simp [FHNode.size]
      constructor
      · intro hzero
        rw [FHNode.forestSize_cons] at hzero
        omega
      · intro himpossible
        cases himpossible

/-- Executable extract-min returns `none` exactly when the root forest is
empty. -/
theorem extractMin_none_iff (h : FH) :
    extractMin h = none ↔ h.roots = [] := by
  constructor
  · intro hextract
    cases hremove : removeMinRoot h.roots with
    | none => exact (removeMinRoot_none_iff h.roots).mp hremove
    | some pair =>
        rcases pair with ⟨z, rest⟩
        simp [extractMin, hremove] at hextract
  · intro hroots
    unfold extractMin
    rw [hroots]
    rfl

/-- On a valid heap, executable extract-min fails exactly when the stored
node count is zero. -/
theorem extractMin_none_iff_size_zero (h : FH) (hvalid : h.Valid) :
    extractMin h = none ↔ h.size = 0 := by
  rw [extractMin_none_iff, hvalid.2.2]
  exact (FHNode.forestSize_eq_zero_iff h.roots).symm

/-- The key set of a node is its root key together with all child-subtree keys. -/
theorem keySet_node_eq (k : Int) (m : Bool) (cs : List FHNode) :
    (FHNode.node k m cs).keySet = {k} ∪ FHNode.forestKeySet cs := by
  rw [forestKeySet_eq_flatMap]
  ext z
  simp [FHNode.keySet, FHNode.keysList, List.mem_toFinset, Finset.mem_union]

/-- Permuting roots does not change the represented forest key set. -/
theorem forestKeySet_eq_of_perm {xs ys : List FHNode} (h : xs.Perm ys) :
    FHNode.forestKeySet xs = FHNode.forestKeySet ys := by
  rw [forestKeySet_eq_flatMap, forestKeySet_eq_flatMap]
  exact List.toFinset_eq_of_perm _ _
    (h.flatMap (fun _ _ => List.Perm.refl _))

/-- Remove a direct child by list index and clear the promoted child's mark. -/
def cutChildAt (t : FHNode) (childIndex : Nat) :
    Option (FHNode × FHNode) :=
  match t with
  | FHNode.node k marked children =>
      match children[childIndex]? with
      | none => none
      | some child =>
          some (markFalse child,
            FHNode.node k marked (children.eraseIdx childIndex))

/-- An indexed child cut splits the original node's key set between the
promoted child and the remaining parent. -/
theorem cutChildAt_keys {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent')) :
    cut.keySet ∪ parent'.keySet = t.keySet := by
  cases t with
  | node k marked children =>
      unfold cutChildAt at hcut
      cases hget : children[i]? with
      | none => simp [hget] at hcut
      | some child =>
          simp [hget] at hcut
          have hcut' : markFalse child = cut := hcut.1
          have hparent' : FHNode.node k marked (children.eraseIdx i) = parent' := hcut.2
          subst cut
          subst parent'
          obtain ⟨hi, hchild⟩ := List.getElem?_eq_some_iff.mp hget
          have hperm : (child :: children.eraseIdx i).Perm children := by
            simpa only [hchild] using List.getElem_cons_eraseIdx_perm hi
          have hforest :
              child.keySet ∪ FHNode.forestKeySet (children.eraseIdx i) =
                FHNode.forestKeySet children := by
            change FHNode.forestKeySet (child :: children.eraseIdx i) =
              FHNode.forestKeySet children
            exact forestKeySet_eq_of_perm hperm
          rw [markFalse_keySet, keySet_node_eq, keySet_node_eq]
          rw [← hforest]
          ac_rfl

/-- An indexed child cut preserves heap order for both the promoted child and
the remaining parent. -/
theorem cutChildAt_heapOrdered {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent'))
    (ht : t.HeapOrdered) :
    cut.HeapOrdered ∧ parent'.HeapOrdered := by
  cases t with
  | node k marked children =>
      cases ht with
      | node hle hall =>
          unfold cutChildAt at hcut
          cases hget : children[i]? with
          | none => simp [hget] at hcut
          | some child =>
              simp [hget] at hcut
              have hcut' : markFalse child = cut := hcut.1
              have hparent' :
                  FHNode.node k marked (children.eraseIdx i) = parent' := hcut.2
              subst cut
              subst parent'
              obtain ⟨hi, hchild⟩ := List.getElem?_eq_some_iff.mp hget
              have hmem : child ∈ children := by
                have hmemAt : children[i] ∈ children := List.getElem_mem hi
                simpa [hchild] using hmemAt
              constructor
              · exact markFalse_heapOrdered child (hall child hmem)
              · exact FHNode.HeapOrdered.node
                  (fun c hc => hle c (mem_eraseIdx_of_mem i hc))
                  (fun c hc => hall c (mem_eraseIdx_of_mem i hc))

/-- An indexed child cut preserves structural wellformedness for both the
promoted child and the remaining parent. -/
theorem cutChildAt_wellformed {t cut parent' : FHNode} {i : Nat}
    (hcut : cutChildAt t i = some (cut, parent'))
    (ht : t.Wellformed) :
    cut.Wellformed ∧ parent'.Wellformed := by
  cases t with
  | node k marked children =>
      unfold cutChildAt at hcut
      cases hget : children[i]? with
      | none => simp [hget] at hcut
      | some child =>
          simp [hget] at hcut
          have hcut' : markFalse child = cut := hcut.1
          have hparent' :
              FHNode.node k marked (children.eraseIdx i) = parent' := hcut.2
          subst cut
          subst parent'
          obtain ⟨hi, hchild⟩ := List.getElem?_eq_some_iff.mp hget
          have hmem : child ∈ children := by
            have hmemAt : children[i] ∈ children := List.getElem_mem hi
            simpa [hchild] using hmemAt
          have htree : (FTree.node (children.map FHNode.toFTree)).Wellformed := by
            simpa [FHNode.Wellformed, FHNode.toFTree] using ht
          cases htree with
          | node hdeg hall =>
              have hchildTree : child.toFTree.Wellformed :=
                hall child.toFTree (List.mem_map.mpr ⟨child, hmem, rfl⟩)
              have hchildWellformed : child.Wellformed := by
                simpa [FHNode.Wellformed] using hchildTree
              constructor
              · exact markFalse_wellformed child hchildWellformed
              · have hw' :
                    (FTree.node
                      ((children.map FHNode.toFTree).eraseIdx i)).Wellformed :=
                    FTree.wellformed_remove_index
                      (FTree.Wellformed.node hdeg hall) i
                      (by simpa [List.length_map] using hi)
                have hmap :
                    (children.eraseIdx i).map FHNode.toFTree =
                      (children.map FHNode.toFTree).eraseIdx i :=
                  map_eraseIdx FHNode.toFTree children i
                simpa [FHNode.Wellformed, FHNode.toFTree, hmap] using hw'

/-- Cut a direct child of an indexed root and promote it into the root list.
The stored node count is unchanged because the operation only moves a node. -/
def cutRootChildAt (h : FH) (rootIndex childIndex : Nat) : Option FH :=
  match h.roots[rootIndex]? with
  | none => none
  | some parent =>
      match cutChildAt parent childIndex with
      | none => none
      | some (cut, parent') =>
          some
            { roots := cut :: h.roots.set rootIndex parent'
            , size := h.size }

/-- Replacing a present forest root satisfies the key-set union balance used
to lift local CUT facts to the complete root forest. -/
theorem forestKeySet_set_balance {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old) :
    FHNode.forestKeySet (roots.set i new) ∪ old.keySet =
      FHNode.forestKeySet roots ∪ new.keySet := by
  induction roots generalizing i with
  | nil => simp at hget
  | cons root roots ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hroot
          subst old
          simp only [List.set_cons_zero]
          change (new.keySet ∪ FHNode.forestKeySet roots) ∪ root.keySet =
            (root.keySet ∪ FHNode.forestKeySet roots) ∪ new.keySet
          ac_rfl
      | succ i =>
          simp only [List.getElem?_cons_succ] at hget
          have hbalance := ih hget
          simp only [List.set_cons_succ]
          change (root.keySet ∪ FHNode.forestKeySet (roots.set i new)) ∪
              old.keySet =
            (root.keySet ∪ FHNode.forestKeySet roots) ∪ new.keySet
          calc
            _ = root.keySet ∪
                (FHNode.forestKeySet (roots.set i new) ∪ old.keySet) :=
              Finset.union_assoc _ _ _
            _ = root.keySet ∪
                (FHNode.forestKeySet roots ∪ new.keySet) := by rw [hbalance]
            _ = _ := (Finset.union_assoc _ _ _).symm

/-- If a replacement root and an extra promoted root partition the old root,
then replacing and prepending preserves the whole forest key set. -/
theorem forestKeySet_cut_set {roots : List FHNode} {i : Nat}
    {old cut new : FHNode} (hget : roots[i]? = some old)
    (hkeys : cut.keySet ∪ new.keySet = old.keySet) :
    cut.keySet ∪ FHNode.forestKeySet (roots.set i new) =
      FHNode.forestKeySet roots := by
  induction roots generalizing i with
  | nil => simp at hget
  | cons root roots ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hroot
          subst old
          simp only [List.set_cons_zero]
          rw [FHNode.forestKeySet_cons, FHNode.forestKeySet_cons]
          rw [← Finset.union_assoc, hkeys]
      | succ i =>
          simp only [List.getElem?_cons_succ] at hget
          have htail := ih hget
          simp only [List.set_cons_succ]
          change cut.keySet ∪
              (root.keySet ∪ FHNode.forestKeySet (roots.set i new)) =
            root.keySet ∪ FHNode.forestKeySet roots
          ext z
          have htailMem := Finset.ext_iff.mp htail z
          simp only [Finset.mem_union] at htailMem ⊢
          tauto

/-- Replacing a present root by a good root preserves structural goodness of
the root forest. -/
theorem forestGood_set {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old)
    (hroots : FHNode.ForestGood roots)
    (hnew : new.HeapOrdered ∧ new.Wellformed) :
    FHNode.ForestGood (roots.set i new) := by
  induction roots generalizing i with
  | nil => simp at hget
  | cons root roots ih =>
      have hrootOrdered : root.HeapOrdered := hroots.1 root (by simp)
      have hrootWellformed : root.Wellformed := hroots.2 root (by simp)
      have htail : FHNode.ForestGood roots :=
        ⟨(fun t ht => hroots.1 t (by simp [ht])),
          (fun t ht => hroots.2 t (by simp [ht]))⟩
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hget
          simp only [List.set_cons_zero]
          exact
            ⟨(fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hnew.1
                · exact htail.1 t ht),
              (fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hnew.2
                · exact htail.2 t ht)⟩
      | succ i =>
          simp only [List.getElem?_cons_succ] at hget
          have htailSet := ih hget htail
          simp only [List.set_cons_succ]
          exact
            ⟨(fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hrootOrdered
                · exact htailSet.1 t ht),
              (fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hrootWellformed
                · exact htailSet.2 t ht)⟩

/-- A successful heap-level CUT preserves the stored node count. -/
theorem cutRootChildAt_size {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    h'.size = h.size := by
  unfold cutRootChildAt at hcut
  cases hparent : h.roots[ri]? with
  | none => simp [hparent] at hcut
  | some parent =>
      cases hlocal : cutChildAt parent ci with
      | none => simp [hparent, hlocal] at hcut
      | some result =>
          rcases result with ⟨cut, parent'⟩
          simp [hparent, hlocal] at hcut
          subst h'
          rfl

/-- A successful heap-level CUT adds exactly one root. -/
theorem cutRootChildAt_roots_length {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    h'.roots.length = h.roots.length + 1 := by
  unfold cutRootChildAt at hcut
  cases hparent : h.roots[ri]? with
  | none => simp [hparent] at hcut
  | some parent =>
      cases hlocal : cutChildAt parent ci with
      | none => simp [hparent, hlocal] at hcut
      | some result =>
          rcases result with ⟨cut, parent'⟩
          simp [hparent, hlocal] at hcut
          subst h'
          simp [List.length_set]

/-- A successful heap-level CUT preserves the complete heap key set. -/
theorem cutRootChildAt_keys {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h') :
    keys h' = keys h := by
  unfold cutRootChildAt at hcut
  cases hparent : h.roots[ri]? with
  | none => simp [hparent] at hcut
  | some parent =>
      cases hlocal : cutChildAt parent ci with
      | none => simp [hparent, hlocal] at hcut
      | some result =>
          rcases result with ⟨cut, parent'⟩
          simp [hparent, hlocal] at hcut
          subst h'
          change cut.keySet ∪
              FHNode.forestKeySet (h.roots.set ri parent') =
            FHNode.forestKeySet h.roots
          exact forestKeySet_cut_set hparent (cutChildAt_keys hlocal)

/-- A successful heap-level CUT preserves heap order and structural
wellformedness of the complete root forest. -/
theorem cutRootChildAt_good {h h' : FH} {ri ci : Nat}
    (hcut : cutRootChildAt h ri ci = some h')
    (hgood : FHNode.ForestGood h.roots) :
    FHNode.ForestGood h'.roots := by
  unfold cutRootChildAt at hcut
  cases hparent : h.roots[ri]? with
  | none => simp [hparent] at hcut
  | some parent =>
      cases hlocal : cutChildAt parent ci with
      | none => simp [hparent, hlocal] at hcut
      | some result =>
          rcases result with ⟨cut, parent'⟩
          simp [hparent, hlocal] at hcut
          subst h'
          obtain ⟨hri, hparentEq⟩ := List.getElem?_eq_some_iff.mp hparent
          have hparentMem : parent ∈ h.roots := by
            have hmemAt : h.roots[ri] ∈ h.roots := List.getElem_mem hri
            simpa [hparentEq] using hmemAt
          have hordered := cutChildAt_heapOrdered hlocal
            (hgood.1 parent hparentMem)
          have hwellformed := cutChildAt_wellformed hlocal
            (hgood.2 parent hparentMem)
          have hset : FHNode.ForestGood (h.roots.set ri parent') :=
            forestGood_set hparent hgood ⟨hordered.2, hwellformed.2⟩
          exact
            ⟨(fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hordered.1
                · exact hset.1 t ht),
              (fun t ht => by
                simp only [List.mem_cons] at ht
                rcases ht with rfl | ht
                · exact hwellformed.1
                · exact hset.2 t ht)⟩

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

/-- Replacing a present forest root satisfies the corresponding mark-count
balance equation. -/
theorem forestMarks_set_add {roots : List FHNode} {i : Nat}
    {old new : FHNode} (hget : roots[i]? = some old) :
    FHNode.forestMarks (roots.set i new) + old.marks =
      FHNode.forestMarks roots + new.marks := by
  induction roots generalizing i with
  | nil => simp at hget
  | cons root roots ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero] at hget
          injection hget with hroot
          subst old
          simp only [List.set_cons_zero, FHNode.forestMarks_cons]
          omega
      | succ i =>
          simp only [List.getElem?_cons_succ] at hget
          have hbalance := ih hget
          simp only [List.set_cons_succ, FHNode.forestMarks_cons]
          omega

/-- A local indexed CUT preserves all marks except the selected child's root
mark, which is cleared on promotion. -/
theorem cutChildAt_marks_add {parent child cut parent' : FHNode} {i : Nat}
    (hchild : parent.children[i]? = some child)
    (hcut : cutChildAt parent i = some (cut, parent')) :
    cut.marks + parent'.marks + (if child.marked then 1 else 0) =
      parent.marks := by
  cases parent with
  | node k marked children =>
      simp only [FHNode.children_node] at hchild
      unfold cutChildAt at hcut
      simp [hchild] at hcut
      have hcut' : markFalse child = cut := hcut.1
      have hparent' :
          FHNode.node k marked (children.eraseIdx i) = parent' := hcut.2
      subst cut
      subst parent'
      obtain ⟨hi, hchildAt⟩ := List.getElem?_eq_some_iff.mp hchild
      have hperm : (child :: children.eraseIdx i).Perm children := by
        simpa only [hchildAt] using List.getElem_cons_eraseIdx_perm hi
      have hsum :
          child.marks + ((children.eraseIdx i).map FHNode.marks).sum =
            (children.map FHNode.marks).sum := by
        simpa using (hperm.map FHNode.marks).sum_eq
      have hmark := markFalse_marks_add child
      simp only [FHNode.marks_node]
      omega

/-- At heap level, CUT removes exactly the selected child's old root-mark
contribution from the total marked-node count. -/
theorem cutRootChildAt_forestMarks_add {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    FHNode.forestMarks h'.roots + (if child.marked then 1 else 0) =
      FHNode.forestMarks h.roots := by
  unfold cutRootChildAt at hcut
  rw [hparent] at hcut
  cases hlocal : cutChildAt parent ci with
  | none => simp [hlocal] at hcut
  | some result =>
      rcases result with ⟨cut, parent'⟩
      simp [hlocal] at hcut
      subst h'
      have hset := forestMarks_set_add (new := parent') hparent
      have hnode := cutChildAt_marks_add hchild hlocal
      simp only [FHNode.forestMarks_cons]
      omega

/-- Exact potential change of a heap-level direct-child CUT.  The new root
contributes `+1`; clearing a previously marked child contributes `-2`. -/
theorem cutRootChildAt_potential_eq {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    potential h' = potential h + 1 -
      2 * Int.ofNat (if child.marked then 1 else 0) := by
  have hlength := cutRootChildAt_roots_length hcut
  have hmarks := cutRootChildAt_forestMarks_add hparent hchild hcut
  unfold potential
  cases hmarked : child.marked <;> simp [hmarked] at hmarks ⊢ <;> omega

/-- A heap-level direct-child CUT raises the standard potential by at most
one. -/
theorem cutRootChildAt_potential_le {h h' : FH}
    {parent child : FHNode} {ri ci : Nat}
    (hparent : h.roots[ri]? = some parent)
    (hchild : parent.children[ci]? = some child)
    (hcut : cutRootChildAt h ri ci = some h') :
    potential h' ≤ potential h + 1 := by
  rw [cutRootChildAt_potential_eq hparent hchild hcut]
  cases hmarked : child.marked <;> simp [hmarked]
