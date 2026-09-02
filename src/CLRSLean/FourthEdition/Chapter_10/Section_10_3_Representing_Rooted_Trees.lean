import Mathlib

/-!
# CLRS Section 10.4 - Representing rooted trees

CLRS §10.4 shows how to store a rooted tree with an *unbounded* branching factor
using only two pointers per node -- the **left-child, right-sibling (LCRS)**
representation -- instead of a per-node child array.  In the textbook,
{lit}`x.left-child` points to the leftmost child of {lit}`x` and
{lit}`x.right-sibling` points to the next sibling of {lit}`x` to its right.

This section formalizes the LCRS scheme as a purely *functional*,
information-preserving encoding between two data models:

- {lit}`RoseTree`: a multiway rooted tree -- a label together with a
  {lit}`List (RoseTree α)` of children (arbitrary branching factor).
- {lit}`LCRSTree`: a binary tree whose left subtree means "leftmost child" and
  whose right subtree means "next sibling".

The clean correctness statement is a *round-trip isomorphism* between a rooted
*forest* (an ordered list of sibling trees) and its LCRS binary encoding.

Main results:

- {lit}`toLCRSForest` / {lit}`ofLCRSForest`: total encode/decode between a forest
  ({lit}`List (RoseTree α)`) and an {lit}`LCRSTree α`.
- Theorem {lit}`ofLCRSForest_toLCRSForest` and {lit}`toLCRSForest_ofLCRSForest`:
  the two maps are mutually inverse, so the LCRS binary encoding is a faithful,
  information-preserving representation of a rooted forest.
- {lit}`lcrsEquiv`: the round trip packaged as an {lit}`Equiv` (bijection)
  between {lit}`List (RoseTree α)` and {lit}`LCRSTree α`.
- Theorem {lit}`ofLCRS_toLCRS`: the single-tree round trip
  {lit}`ofLCRS (toLCRS t) = t`.
- Theorem {lit}`toLCRSForest_preorder`: the encoding preserves the preorder label
  sequence, and {lit}`toLCRSForest_numNodes`: it preserves the node count.

Status: {lit}`proved`.  This is the functional/representational core of §10.4; the
pointer/free-list RAM layer for Chapter 10 stays under the imperative-memory
epic and is out of scope here.

Notation conventions used in this section:

- {lit}`α` : the node-label type
- a *forest* is a {lit}`List (RoseTree α)` -- an ordered list of sibling subtrees
-/

namespace CLRS
namespace Chapter10

universe u

/-! ## Models -/

/--
A {lit}`RoseTree α` is a multiway rooted tree: a label of type {lit}`α` together
with an ordered list of child subtrees (arbitrary branching factor).  This is the
"logical" rooted tree of CLRS §10.4, before any pointer representation is
chosen.
-/
inductive RoseTree (α : Type u) where
  | node : α → List (RoseTree α) → RoseTree α

/--
An {lit}`LCRSTree α` is the binary tree used for the left-child / right-sibling
representation of CLRS §10.4.  {lit}`node a l r` stores label {lit}`a`; its left
subtree {lit}`l` encodes {lit}`a`'s children (its leftmost child together with
that child's sibling chain) and its right subtree {lit}`r` encodes {lit}`a`'s own
right siblings.  {lit}`nil` is the null pointer.
-/
inductive LCRSTree (α : Type u) where
  | nil : LCRSTree α
  | node : α → LCRSTree α → LCRSTree α → LCRSTree α

/-! ## Encoding and decoding -/

/--
Encode a *forest* (an ordered list of sibling rose trees) into a single
{lit}`LCRSTree`.  The head tree {lit}`node a cs` becomes an LCRS node whose left
subtree encodes its children {lit}`cs` and whose right subtree encodes the
remaining siblings {lit}`ts`.  This is the recursive heart of the LCRS
representation (CLRS §10.4).
-/
def toLCRSForest : List (RoseTree α) → LCRSTree α
  | [] => .nil
  | RoseTree.node a cs :: ts => .node a (toLCRSForest cs) (toLCRSForest ts)
termination_by l => sizeOf l
decreasing_by all_goals (simp_wf <;> omega)

/--
Encode a single rooted tree: {lit}`toLCRS t` is the forest encoding of the
one-tree forest {lit}`[t]`, i.e. an LCRS node whose right-sibling pointer is null.
-/
def toLCRS (t : RoseTree α) : LCRSTree α :=
  toLCRSForest [t]

/--
Decode an {lit}`LCRSTree` back into a forest.  An LCRS node {lit}`node a l r`
yields the rose tree {lit}`node a (ofLCRSForest l)` followed by the decoded
sibling chain {lit}`ofLCRSForest r`.  This is structurally recursive on the
binary tree.
-/
def ofLCRSForest : LCRSTree α → List (RoseTree α)
  | .nil => []
  | .node a l r => RoseTree.node a (ofLCRSForest l) :: ofLCRSForest r

/--
Decode an {lit}`LCRSTree` into a single rooted tree, dropping any right-sibling
chain of the root.  The null tree maps to the junk value {lit}`node default []`
(hence the {lit}`[Inhabited α]` assumption), which makes the function total; on
genuine single-tree encodings (whose root has a null right sibling) it is the
exact inverse of {lit}`toLCRS`.
-/
def ofLCRS [Inhabited α] : LCRSTree α → RoseTree α
  | .nil => RoseTree.node default []
  | .node a l _ => RoseTree.node a (ofLCRSForest l)

/-! ## Round-trip isomorphism (headline) -/

/--
**Decode ∘ encode = id on forests.**  Encoding a forest to its LCRS binary tree
and decoding it back returns the original forest: the LCRS representation loses
no information (CLRS §10.4).
-/
theorem ofLCRSForest_toLCRSForest (f : List (RoseTree α)) :
    ofLCRSForest (toLCRSForest f) = f := by
  induction f using toLCRSForest.induct with
  | case1 => simp [toLCRSForest, ofLCRSForest]
  | case2 a cs ts ihcs ihts =>
      simp [toLCRSForest, ofLCRSForest, ihcs, ihts]

/--
**Encode ∘ decode = id on LCRS trees.**  Decoding an {lit}`LCRSTree` to a forest
and re-encoding it returns the original binary tree: the decode map hits every
LCRS tree, so the encoding is onto.
-/
theorem toLCRSForest_ofLCRSForest (b : LCRSTree α) :
    toLCRSForest (ofLCRSForest b) = b := by
  induction b with
  | nil => simp [ofLCRSForest, toLCRSForest]
  | node a l r ihl ihr =>
      simp [ofLCRSForest, toLCRSForest, ihl, ihr]

/--
The LCRS round trip packaged as an {lit}`Equiv`: the forest encoding
{lit}`toLCRSForest` is a *bijection* from rooted forests
({lit}`List (RoseTree α)`) to LCRS binary trees ({lit}`LCRSTree α`), with inverse
{lit}`ofLCRSForest`.  This is the precise sense in which the left-child /
right-sibling scheme of CLRS §10.4 is a faithful representation.
-/
def lcrsEquiv : List (RoseTree α) ≃ LCRSTree α where
  toFun := toLCRSForest
  invFun := ofLCRSForest
  left_inv := ofLCRSForest_toLCRSForest
  right_inv := toLCRSForest_ofLCRSForest

/--
**Single-tree round trip.**  Decoding the LCRS encoding of one rooted tree
returns that tree exactly: {lit}`ofLCRS (toLCRS t) = t`.  A corollary of the
forest-level round trip {lit}`ofLCRSForest_toLCRSForest`.
-/
theorem ofLCRS_toLCRS [Inhabited α] (t : RoseTree α) :
    ofLCRS (toLCRS t) = t := by
  cases t with
  | node a cs =>
      simp [toLCRS, toLCRSForest, ofLCRS, ofLCRSForest_toLCRSForest]

/-! ## Structure preservation -/

/--
Preorder label sequence of an {lit}`LCRSTree`: visit the node, then its left
subtree (children), then its right subtree (siblings).  This is the order in
which an LCRS traversal reads the labels.
-/
def LCRSTree.preorder : LCRSTree α → List α
  | .nil => []
  | .node a l r => a :: (LCRSTree.preorder l ++ LCRSTree.preorder r)

/--
Preorder label sequence of a rooted *forest*: for each tree in order emit its
root label, then recurse into its children, then continue with the following
siblings.  This is the canonical reading order of the multiway forest.
-/
def forestPreorder : List (RoseTree α) → List α
  | [] => []
  | RoseTree.node a cs :: ts => a :: (forestPreorder cs ++ forestPreorder ts)
termination_by l => sizeOf l
decreasing_by all_goals (simp_wf <;> omega)

/--
**Preorder preservation (structure preservation).**  The LCRS encoding preserves
the preorder label sequence of the forest: reading the binary encoding in
node/left/right order reproduces the forest's canonical reading order.  In
particular the encoding reorders no labels and drops none.
-/
theorem toLCRSForest_preorder (f : List (RoseTree α)) :
    (toLCRSForest f).preorder = forestPreorder f := by
  induction f using toLCRSForest.induct with
  | case1 => simp [toLCRSForest, LCRSTree.preorder, forestPreorder]
  | case2 a cs ts ihcs ihts =>
      simp [toLCRSForest, LCRSTree.preorder, forestPreorder, ihcs, ihts]

/-- Number of internal {lit}`node`s in an {lit}`LCRSTree`. -/
def LCRSTree.numNodes : LCRSTree α → Nat
  | .nil => 0
  | .node _ l r => LCRSTree.numNodes l + LCRSTree.numNodes r + 1

/-- The node count of an {lit}`LCRSTree` equals the length of its preorder sequence. -/
theorem LCRSTree.numNodes_eq_length_preorder (b : LCRSTree α) :
    b.numNodes = b.preorder.length := by
  induction b with
  | nil => simp [LCRSTree.numNodes, LCRSTree.preorder]
  | node a l r ihl ihr =>
      simp only [LCRSTree.numNodes, LCRSTree.preorder, List.length_cons,
        List.length_append, ihl, ihr]

/--
**Node-count preservation.**  The LCRS binary encoding of a forest has exactly
one binary node per rose-tree node, i.e. the encoding introduces no extra nodes
and loses none.
-/
theorem toLCRSForest_numNodes (f : List (RoseTree α)) :
    (toLCRSForest f).numNodes = (forestPreorder f).length := by
  rw [LCRSTree.numNodes_eq_length_preorder, toLCRSForest_preorder]

/--
Single-tree preorder preservation: the LCRS encoding of one rooted tree reads
back the forest preorder of the one-tree forest {lit}`[t]`.
-/
theorem toLCRS_preorder (t : RoseTree α) :
    (toLCRS t).preorder = forestPreorder [t] := by
  simp only [toLCRS, toLCRSForest_preorder]

end Chapter10
end CLRS
