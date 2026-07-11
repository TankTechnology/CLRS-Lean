import Mathlib
import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-!
# CLRS Section 14.1 - Order-statistic trees

This section gives the first augmentation proof for CLRS-Lean.  An
order-statistic tree stores, at every node, a size field intended to equal the
number of nodes in that subtree.  The operation {lit}`osSelect?` uses the
stored size of the left child to implement rank selection.

The file separates the executable augmented operation from its ideal
mathematical specification:

* {lit}`storedSize` reads the cached field;
* {lit}`realSize` recomputes the mathematical subtree size;
* {lit}`WellSized` says every cached field is correct;
* {lit}`rankSelect?` is the ideal selector using recomputed sizes;
* {lit}`osSelect?` is the augmented selector using cached sizes.

Main results:

* Theorem {lit}`storedSize_eq_realSize_of_wellSized`: a well-sized tree has a
  correct root size field.
* Theorem {lit}`realSize_recomputeSizes`: recomputing cached size fields
  preserves the mathematical subtree size.
* Theorem {lit}`recomputeSizes_wellSized`: recomputing size fields establishes
  the augmentation invariant.
* Theorem {lit}`keys_recomputeSizes`: recomputing size fields preserves the
  inorder key sequence.
* Theorem {lit}`rankSelect?_recomputeSizes`: recomputing size fields preserves
  the ideal rank-selection result.
* Theorems {lit}`keys_rotateLeft` and {lit}`keys_rotateRight`: rotations
  preserve the inorder key sequence.
* Theorems {lit}`rotateLeft_wellSized` and {lit}`rotateRight_wellSized`:
  rotations with local size recomputation preserve the size augmentation
  invariant.
* Theorems {lit}`storedSize_rotateLeft_of_wellSized` and
  {lit}`storedSize_rotateRight_of_wellSized`: rotations preserve the cached
  root size of a well-sized tree.
* Theorems {lit}`rankSelect?_rotateLeft` and {lit}`rankSelect?_rotateRight`:
  rotations preserve the ideal rank-selection result.
* Theorem {lit}`osSelect?_eq_rankSelect?_of_wellSized`: on a well-sized tree,
  the augmented selector agrees with the ideal rank selector.
* Theorems {lit}`osSelect?_rotateLeft_eq_rankSelect?_of_wellSized` and
  {lit}`osSelect?_rotateRight_eq_rankSelect?_of_wellSized`: after a
  size-preserving rotation, the augmented selector still implements the
  original ideal rank selector.
* Theorems {lit}`rotateLeft_recomputeSizes_wellSized` and
  {lit}`rotateRight_recomputeSizes_wellSized`: recompute-then-rotate produces a
  well-sized tree from any input tree.
* Theorems {lit}`osSelect?_rotateLeft_recomputeSizes_eq_rankSelect?` and
  {lit}`osSelect?_rotateRight_recomputeSizes_eq_rankSelect?`: recompute-then-
  rotate preserves the augmented selector's agreement with the original ideal
  rank selector.

## Size augmentation through executable red-black insertion

The second half of this file closes the "stored-field refinement" gap by
threading the size augmentation through an *executable* red-black insertion.
The augmented tree {lit}`OSRBTree` caches both a node colour and a subtree size.
Its Okasaki-style {lit}`balanceLeft`/{lit}`balanceRight`/{lit}`insertFixup`/
{lit}`insert` mirror the Chapter 13 red-black operations node-for-node, but every
reconstructed node is built by the smart constructor {lit}`mk`, which recomputes
the cached size from its children.  Two bridges connect this to the existing
Chapter 13 development and to the ideal order-statistic semantics:

* Theorem {lit}`OSRBTree.wellSized_insert`: **the augmentation invariant survives
  through balancing** — inserting into a well-sized tree yields a well-sized
  tree, so every cached size field is correct after the red-black rebalancing
  (CLRS 14.1 maintained through {lit}`RB-INSERT`).
* Theorem {lit}`OSRBTree.osSelect?_insert_eq_rankSelect?`: after insertion the
  augmented (cached-size) selector still agrees with the ideal recomputed-size
  rank selector.
* Theorem {lit}`OSRBTree.storedSize_insert`: the cached root size is correct
  after insertion.
* Theorem {lit}`OSRBTree.toRB_insert`: erasing the size field commutes with
  insertion — the augmented insert refines the *executable* Chapter 13
  {lit}`RBTree.insert` exactly.  Through this refinement, Chapter 13's shape,
  membership, and height theorems transfer to the augmented tree
  (Theorems {lit}`OSRBTree.redBlackShape_toRB_insert` and
  {lit}`OSRBTree.mem_keys_insert`).

Current gaps:

* Deletion is not yet threaded through the augmentation (it depends on the
  Chapter 13 executable {lit}`RB-DELETE` loop, which is still local-case only).
* Interval trees and the general augmentation theorem remain future targets.
-/

namespace CLRS
namespace Chapter14

/-! ## Augmented tree model -/

/-- A binary tree whose internal nodes cache their subtree size. -/
inductive OSTree where
  | empty : OSTree
  | node : OSTree → Nat → Nat → OSTree → OSTree
  deriving Repr, DecidableEq

namespace OSTree

/-- Mathematical inorder traversal of the keys, ignoring cached sizes. -/
def keys : OSTree → List Nat
  | empty => []
  | node left key _size right => keys left ++ [key] ++ keys right

/-- The cached size stored at the root.  Empty trees have cached size zero. -/
def storedSize : OSTree → Nat
  | empty => 0
  | node _left _key size _right => size

/-- The mathematical size obtained by recursively counting nodes. -/
def realSize : OSTree → Nat
  | empty => 0
  | node left _key _size right => realSize left + realSize right + 1

/-- Every cached size field agrees with the mathematical subtree size. -/
def WellSized : OSTree → Prop
  | empty => True
  | node left _key size right =>
      WellSized left ∧ WellSized right ∧
        size = realSize left + realSize right + 1

/-- Recompute every cached size field from the children upward. -/
def recomputeSizes : OSTree → OSTree
  | empty => empty
  | node left key _size right =>
      let left' := recomputeSizes left
      let right' := recomputeSizes right
      node left' key (realSize left' + realSize right' + 1) right'

/-! ## Local rotations -/

/--
Left rotation with local size recomputation.  If the right child is empty, the
tree is left unchanged.
-/
def rotateLeft : OSTree → OSTree
  | node a x _ (node b y _ c) =>
      let left' := node a x (realSize a + realSize b + 1) b
      node left' y (realSize left' + realSize c + 1) c
  | t => t

/--
Right rotation with local size recomputation.  If the left child is empty, the
tree is left unchanged.
-/
def rotateRight : OSTree → OSTree
  | node (node a x _ b) y _ c =>
      let right' := node b y (realSize b + realSize c + 1) c
      node a x (realSize a + realSize right' + 1) right'
  | t => t

/-! ## Selectors -/

/--
The ideal rank selector, using mathematically recomputed subtree sizes.
Ranks are zero-based: rank zero returns the first inorder key.
-/
def rankSelect? : OSTree → Nat → Option Nat
  | empty, _ => none
  | node left key _size right, i =>
      if i < realSize left then
        rankSelect? left i
      else if i = realSize left then
        some key
      else
        rankSelect? right (i - realSize left - 1)

/--
The augmented order-statistic selector, using cached subtree sizes rather than
recomputing them.  The main theorem states that this agrees with
{lit}`rankSelect?` whenever the cached fields are well-sized.
-/
def osSelect? : OSTree → Nat → Option Nat
  | empty, _ => none
  | node left key _size right, i =>
      if i < storedSize left then
        osSelect? left i
      else if i = storedSize left then
        some key
      else
        osSelect? right (i - storedSize left - 1)

/-! ## Augmentation correctness -/

/-- A well-sized tree has a correct root size field. -/
theorem storedSize_eq_realSize_of_wellSized {t : OSTree}
    (h : WellSized t) : storedSize t = realSize t := by
  cases t with
  | empty =>
      rfl
  | node left key size right =>
      exact h.2.2

/-- Recomputing cached size fields preserves the inorder key sequence. -/
theorem keys_recomputeSizes (t : OSTree) :
    keys (recomputeSizes t) = keys t := by
  induction t with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, keys, ihLeft, ihRight]

/-- Recomputing cached size fields preserves the mathematical subtree size. -/
theorem realSize_recomputeSizes (t : OSTree) :
    realSize (recomputeSizes t) = realSize t := by
  induction t with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, realSize, ihLeft, ihRight]

/-- Recomputing cached size fields establishes the size augmentation invariant. -/
theorem recomputeSizes_wellSized (t : OSTree) :
    WellSized (recomputeSizes t) := by
  induction t with
  | empty =>
      trivial
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, WellSized, ihLeft, ihRight]

/-! ## Rotation correctness for the size augmentation -/

/-- Left rotation preserves the inorder key sequence. -/
theorem keys_rotateLeft (t : OSTree) :
    keys (rotateLeft t) = keys t := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          simp [rotateLeft, keys, List.append_assoc]

/-- Right rotation preserves the inorder key sequence. -/
theorem keys_rotateRight (t : OSTree) :
    keys (rotateRight t) = keys t := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          simp [rotateRight, keys, List.append_assoc]

/-- Left rotation preserves the mathematical subtree size. -/
theorem realSize_rotateLeft (t : OSTree) :
    realSize (rotateLeft t) = realSize t := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          simp [rotateLeft, realSize]
          omega

/-- Right rotation preserves the mathematical subtree size. -/
theorem realSize_rotateRight (t : OSTree) :
    realSize (rotateRight t) = realSize t := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          simp [rotateRight, realSize]
          omega

/-- Left rotation preserves the cached root size of a well-sized tree. -/
theorem storedSize_rotateLeft_of_wellSized {t : OSTree}
    (h : WellSized t) :
    storedSize (rotateLeft t) = storedSize t := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          rcases h with ⟨_ha, _hRight, hSize⟩
          simp [rotateLeft, storedSize, realSize] at hSize ⊢
          omega

/-- Right rotation preserves the cached root size of a well-sized tree. -/
theorem storedSize_rotateRight_of_wellSized {t : OSTree}
    (h : WellSized t) :
    storedSize (rotateRight t) = storedSize t := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          rcases h with ⟨_hLeft, _hc, hSize⟩
          simp [rotateRight, storedSize, realSize] at hSize ⊢
          omega

/-- Left rotation preserves ideal rank selection. -/
theorem rankSelect?_rotateLeft (t : OSTree) (i : Nat) :
    rankSelect? (rotateLeft t) i = rankSelect? t i := by
  cases t with
  | empty =>
      rfl
  | node a x sx right =>
      cases right with
      | empty =>
          rfl
      | node b y sy c =>
          by_cases hiA : i < realSize a
          · have hiLeft : i < realSize a + realSize b + 1 := by omega
            simp [rotateLeft, rankSelect?, realSize, hiA, hiLeft]
          · by_cases hiEqA : i = realSize a
            · have hiLeft : i < realSize a + realSize b + 1 := by omega
              simp [rotateLeft, rankSelect?, realSize, hiEqA]
            · by_cases hiLeft : i < realSize a + realSize b + 1
              · have hjLt : i - realSize a - 1 < realSize b := by omega
                simp [rotateLeft, rankSelect?, realSize, hiA, hiEqA, hiLeft, hjLt]
              · have hjNotLt : ¬ i - realSize a - 1 < realSize b := by omega
                by_cases hjEq : i - realSize a - 1 = realSize b
                · have hiEqLeft : i = realSize a + realSize b + 1 := by omega
                  subst i
                  have hNotLtA :
                      ¬ realSize a + realSize b + 1 < realSize a := by
                    omega
                  have hNotEqA :
                      ¬ realSize a + realSize b + 1 = realSize a := by
                    omega
                  have hEqB :
                      realSize a + realSize b + 1 - realSize a - 1 = realSize b := by
                    omega
                  simp [rotateLeft, rankSelect?, realSize, hNotLtA, hNotEqA, hEqB]
                · have hiNeLeft : i ≠ realSize a + realSize b + 1 := by omega
                  have hIndex :
                      i - (realSize a + realSize b + 1) - 1 =
                        i - realSize a - 1 - realSize b - 1 := by
                    omega
                  simp [rotateLeft, rankSelect?, realSize, hiA, hiEqA, hiLeft,
                    hjNotLt, hjEq, hiNeLeft, hIndex]

/-- Right rotation preserves ideal rank selection. -/
theorem rankSelect?_rotateRight (t : OSTree) (i : Nat) :
    rankSelect? (rotateRight t) i = rankSelect? t i := by
  cases t with
  | empty =>
      rfl
  | node left y sy c =>
      cases left with
      | empty =>
          rfl
      | node a x sx b =>
          by_cases hiA : i < realSize a
          · have hiLeft : i < realSize a + realSize b + 1 := by omega
            simp [rotateRight, rankSelect?, realSize, hiA, hiLeft]
          · by_cases hiEqA : i = realSize a
            · have hiLeft : i < realSize a + realSize b + 1 := by omega
              simp [rotateRight, rankSelect?, realSize, hiEqA]
            · by_cases hiLeft : i < realSize a + realSize b + 1
              · have hjLt : i - realSize a - 1 < realSize b := by omega
                simp [rotateRight, rankSelect?, realSize, hiA, hiEqA, hiLeft, hjLt]
              · have hjNotLt : ¬ i - realSize a - 1 < realSize b := by omega
                by_cases hjEq : i - realSize a - 1 = realSize b
                · have hiEqLeft : i = realSize a + realSize b + 1 := by omega
                  subst i
                  have hNotLtA :
                      ¬ realSize a + realSize b + 1 < realSize a := by
                    omega
                  have hNotEqA :
                      ¬ realSize a + realSize b + 1 = realSize a := by
                    omega
                  have hEqB :
                      realSize a + realSize b + 1 - realSize a - 1 = realSize b := by
                    omega
                  simp [rotateRight, rankSelect?, realSize, hNotLtA, hNotEqA, hEqB]
                · have hiNeLeft : i ≠ realSize a + realSize b + 1 := by omega
                  have hIndex :
                      i - (realSize a + realSize b + 1) - 1 =
                        i - realSize a - 1 - realSize b - 1 := by
                    omega
                  simp [rotateRight, rankSelect?, realSize, hiA, hiEqA, hiLeft,
                    hjNotLt, hjEq, hiNeLeft, hIndex]

/-- Left rotation with local size recomputation preserves {lit}`WellSized`. -/
theorem rotateLeft_wellSized {t : OSTree}
    (h : WellSized t) : WellSized (rotateLeft t) := by
  cases t with
  | empty =>
      trivial
  | node a x sx right =>
      cases right with
      | empty =>
          simpa [rotateLeft] using h
      | node b y sy c =>
          rcases h with ⟨ha, hRight, _hSize⟩
          rcases hRight with ⟨hb, hc, _hRightSize⟩
          simp [rotateLeft, WellSized, realSize, ha, hb, hc]

/-- Right rotation with local size recomputation preserves {lit}`WellSized`. -/
theorem rotateRight_wellSized {t : OSTree}
    (h : WellSized t) : WellSized (rotateRight t) := by
  cases t with
  | empty =>
      trivial
  | node left y sy c =>
      cases left with
      | empty =>
          simpa [rotateRight] using h
      | node a x sx b =>
          rcases h with ⟨hLeft, hc, _hSize⟩
          rcases hLeft with ⟨ha, hb, _hLeftSize⟩
          simp [rotateRight, WellSized, realSize, ha, hb, hc]

/-- The augmented selector agrees with the ideal selector on well-sized trees. -/
theorem osSelect?_eq_rankSelect?_of_wellSized {t : OSTree} {i : Nat}
    (h : WellSized t) : osSelect? t i = rankSelect? t i := by
  induction t generalizing i with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      rcases h with ⟨hLeft, hRight, hSize⟩
      have hLeftSize : storedSize left = realSize left :=
        storedSize_eq_realSize_of_wellSized hLeft
      by_cases hlt : i < realSize left
      · simp [osSelect?, rankSelect?, hLeftSize, hlt, ihLeft hLeft]
      · by_cases heq : i = realSize left
        · simp [osSelect?, rankSelect?, hLeftSize, heq]
        · simp [osSelect?, rankSelect?, hLeftSize, hlt, heq, ihRight hRight]

/-- Recomputing size fields preserves the ideal rank selector. -/
theorem rankSelect?_recomputeSizes (t : OSTree) (i : Nat) :
    rankSelect? (recomputeSizes t) i = rankSelect? t i := by
  induction t generalizing i with
  | empty =>
      rfl
  | node left key size right ihLeft ihRight =>
      have hLeftSize : realSize (recomputeSizes left) = realSize left :=
        realSize_recomputeSizes left
      by_cases hlt : i < realSize left
      · simp [recomputeSizes, rankSelect?, hLeftSize, hlt, ihLeft]
      · by_cases heq : i = realSize left
        · simp [recomputeSizes, rankSelect?, hLeftSize, heq]
        · simp [recomputeSizes, rankSelect?, hLeftSize, hlt, heq, ihRight]

/--
After a size-preserving left rotation, the augmented selector still implements
the original ideal rank selector.
-/
theorem osSelect?_rotateLeft_eq_rankSelect?_of_wellSized {t : OSTree} {i : Nat}
    (h : WellSized t) :
    osSelect? (rotateLeft t) i = rankSelect? t i := by
  calc
    osSelect? (rotateLeft t) i = rankSelect? (rotateLeft t) i :=
      osSelect?_eq_rankSelect?_of_wellSized (rotateLeft_wellSized h)
    _ = rankSelect? t i := rankSelect?_rotateLeft t i

/--
After a size-preserving right rotation, the augmented selector still implements
the original ideal rank selector.
-/
theorem osSelect?_rotateRight_eq_rankSelect?_of_wellSized {t : OSTree} {i : Nat}
    (h : WellSized t) :
    osSelect? (rotateRight t) i = rankSelect? t i := by
  calc
    osSelect? (rotateRight t) i = rankSelect? (rotateRight t) i :=
      osSelect?_eq_rankSelect?_of_wellSized (rotateRight_wellSized h)
    _ = rankSelect? t i := rankSelect?_rotateRight t i

/--
Recomputing size fields makes the augmented selector agree with the ideal
selector without requiring an external invariant proof.
-/
theorem osSelect?_recomputeSizes_eq_rankSelect? (t : OSTree) (i : Nat) :
    osSelect? (recomputeSizes t) i = rankSelect? (recomputeSizes t) i := by
  exact osSelect?_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized t)

/-- Recomputing size fields and then rotating left produces a well-sized tree. -/
theorem rotateLeft_recomputeSizes_wellSized (t : OSTree) :
    WellSized (rotateLeft (recomputeSizes t)) := by
  exact rotateLeft_wellSized (recomputeSizes_wellSized t)

/-- Recomputing size fields and then rotating right produces a well-sized tree. -/
theorem rotateRight_recomputeSizes_wellSized (t : OSTree) :
    WellSized (rotateRight (recomputeSizes t)) := by
  exact rotateRight_wellSized (recomputeSizes_wellSized t)

/--
After recomputing size fields and rotating left, the augmented selector still
implements the original ideal rank selector.
-/
theorem osSelect?_rotateLeft_recomputeSizes_eq_rankSelect? (t : OSTree) (i : Nat) :
    osSelect? (rotateLeft (recomputeSizes t)) i = rankSelect? t i := by
  calc
    osSelect? (rotateLeft (recomputeSizes t)) i =
        rankSelect? (recomputeSizes t) i :=
      osSelect?_rotateLeft_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized t)
    _ = rankSelect? t i := rankSelect?_recomputeSizes t i

/--
After recomputing size fields and rotating right, the augmented selector still
implements the original ideal rank selector.
-/
theorem osSelect?_rotateRight_recomputeSizes_eq_rankSelect? (t : OSTree) (i : Nat) :
    osSelect? (rotateRight (recomputeSizes t)) i = rankSelect? t i := by
  calc
    osSelect? (rotateRight (recomputeSizes t)) i =
        rankSelect? (recomputeSizes t) i :=
      osSelect?_rotateRight_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized t)
    _ = rankSelect? t i := rankSelect?_recomputeSizes t i

end OSTree

/-! ## Size augmentation through executable red-black insertion

This section threads the size augmentation through an executable red-black
insertion.  The augmented tree {lit}`OSRBTree` caches both a node colour (reusing
{lit}`CLRS.Chapter13.Color`) and a subtree size.  The red-black operations are the
Okasaki-style ones from Chapter 13, but every reconstructed node is built by the
smart constructor {lit}`OSRBTree.mk`, which recomputes the cached size from its
children.  The headline result {lit}`OSRBTree.wellSized_insert` shows that the
size augmentation invariant survives through balancing.
-/

open Chapter13 (Color RBTree)

/--
An augmented red-black tree: every internal node caches a colour and a subtree
size.  This is the red-black refinement of {lit}`OSTree`, adding the colour
field needed to run the Chapter 13 insertion balancer.
-/
inductive OSRBTree where
  | empty : OSRBTree
  | node : Color → OSRBTree → Nat → Nat → OSRBTree → OSRBTree
  deriving Repr, DecidableEq

namespace OSRBTree

/-- Inorder traversal of the keys, ignoring colours and cached sizes. -/
def keys : OSRBTree → List Nat
  | empty => []
  | node _ left key _ right => keys left ++ [key] ++ keys right

/-- The cached size stored at the root.  Empty trees have cached size zero. -/
def storedSize : OSRBTree → Nat
  | empty => 0
  | node _ _ _ size _ => size

/-- The mathematical size obtained by recursively counting nodes. -/
def realSize : OSRBTree → Nat
  | empty => 0
  | node _ left _ _ right => realSize left + realSize right + 1

/-- Every cached size field agrees with the mathematical subtree size. -/
def WellSized : OSRBTree → Prop
  | empty => True
  | node _ left _ size right =>
      WellSized left ∧ WellSized right ∧
        size = realSize left + realSize right + 1

/--
Smart constructor that recomputes the cached size from the children.  Every
node produced by the red-black operations below is built with {lit}`mk`, which is
why the size augmentation invariant is preserved automatically.
-/
def mk (c : Color) (l : OSRBTree) (k : Nat) (r : OSRBTree) : OSRBTree :=
  node c l k (realSize l + realSize r + 1) r

/-- Erase the cached size field, projecting onto the Chapter 13 red-black tree. -/
def toRB : OSRBTree → RBTree
  | empty => RBTree.empty
  | node c l k _ r => RBTree.node c (toRB l) k (toRB r)

/-! ### Basic facts about the smart constructor and the erasure -/

/-- {lit}`mk` recomputes the mathematical subtree size correctly. -/
theorem realSize_mk (c : Color) (l : OSRBTree) (k : Nat) (r : OSRBTree) :
    realSize (mk c l k r) = realSize l + realSize r + 1 := rfl

/-- {lit}`mk` preserves the inorder key sequence. -/
theorem keys_mk (c : Color) (l : OSRBTree) (k : Nat) (r : OSRBTree) :
    keys (mk c l k r) = keys l ++ [k] ++ keys r := rfl

/-- The cached root size of a {lit}`mk` node is the recomputed size. -/
theorem storedSize_mk (c : Color) (l : OSRBTree) (k : Nat) (r : OSRBTree) :
    storedSize (mk c l k r) = realSize l + realSize r + 1 := rfl

/-- A {lit}`mk` node is well-sized whenever both children are. -/
theorem wellSized_mk {c : Color} {l : OSRBTree} {k : Nat} {r : OSRBTree}
    (hl : WellSized l) (hr : WellSized r) : WellSized (mk c l k r) :=
  ⟨hl, hr, rfl⟩

/-- Erasing the cached size of a {lit}`mk` node forgets the size only. -/
theorem toRB_mk (c : Color) (l : OSRBTree) (k : Nat) (r : OSRBTree) :
    toRB (mk c l k r) = RBTree.node c (toRB l) k (toRB r) := rfl

/-- A well-sized tree has a correct root size field. -/
theorem storedSize_eq_realSize_of_wellSized {t : OSRBTree}
    (h : WellSized t) : storedSize t = realSize t := by
  cases t with
  | empty => rfl
  | node c l k s r => exact h.2.2

/-- Erasure relates {lit}`keys` membership to Chapter 13 tree membership. -/
theorem inTree_toRB (y : Nat) (t : OSRBTree) :
    RBTree.InTree y (toRB t) ↔ y ∈ keys t := by
  induction t with
  | empty => simp [toRB, RBTree.InTree, keys]
  | node c l k s r ihl ihr =>
      simp only [toRB, RBTree.InTree, keys, List.append_assoc, List.singleton_append,
        List.mem_append, List.mem_cons, ihl, ihr]
      tauto

/-! ### Selectors -/

/--
The ideal rank selector using mathematically recomputed subtree sizes.  Ranks
are zero-based.
-/
def rankSelect? : OSRBTree → Nat → Option Nat
  | empty, _ => none
  | node _ left key _ right, i =>
      if i < realSize left then
        rankSelect? left i
      else if i = realSize left then
        some key
      else
        rankSelect? right (i - realSize left - 1)

/-- The augmented order-statistic selector using cached subtree sizes. -/
def osSelect? : OSRBTree → Nat → Option Nat
  | empty, _ => none
  | node _ left key _ right, i =>
      if i < storedSize left then
        osSelect? left i
      else if i = storedSize left then
        some key
      else
        osSelect? right (i - storedSize left - 1)

/-- The augmented selector agrees with the ideal selector on well-sized trees. -/
theorem osSelect?_eq_rankSelect?_of_wellSized {t : OSRBTree} {i : Nat}
    (h : WellSized t) : osSelect? t i = rankSelect? t i := by
  induction t generalizing i with
  | empty => rfl
  | node c l k s r ihl ihr =>
      obtain ⟨hLeft, hRight, hSize⟩ := h
      have hLeftSize : storedSize l = realSize l :=
        storedSize_eq_realSize_of_wellSized hLeft
      by_cases hlt : i < realSize l
      · simp [osSelect?, rankSelect?, hLeftSize, hlt, ihl hLeft]
      · by_cases heq : i = realSize l
        · simp [osSelect?, rankSelect?, hLeftSize, heq]
        · simp [osSelect?, rankSelect?, hLeftSize, hlt, heq, ihr hRight]

/-! ### Executable red-black operations with size recomputation -/

/-- Repaint the root black, keeping the cached size fields. -/
def repaintBlack : OSRBTree → OSRBTree
  | empty => empty
  | node _ l k s r => node Color.black l k s r

/--
Okasaki-style rebalance after insertion on the left child, recomputing sizes.
Mirrors {lit}`CLRS.Chapter13.RBTree.balanceLeft`.
-/
def balanceLeft (l : OSRBTree) (y : Nat) (r : OSRBTree) : OSRBTree :=
  match l with
  | node Color.red (node Color.red a w _ b) x _ c =>
      mk Color.red (mk Color.black a w b) x (mk Color.black c y r)
  | node Color.red a w _ (node Color.red b x _ c) =>
      mk Color.red (mk Color.black a w b) x (mk Color.black c y r)
  | _ => mk Color.black l y r

/--
Okasaki-style rebalance after insertion on the right child, recomputing sizes.
Mirrors {lit}`CLRS.Chapter13.RBTree.balanceRight`.
-/
def balanceRight (l : OSRBTree) (y : Nat) (r : OSRBTree) : OSRBTree :=
  match r with
  | node Color.red (node Color.red b x _ c) y' _ d =>
      mk Color.red (mk Color.black l y b) x (mk Color.black c y' d)
  | node Color.red b x _ (node Color.red c y' _ d) =>
      mk Color.red (mk Color.black l y b) x (mk Color.black c y' d)
  | _ => mk Color.black l y r

/-- Insertion fixup: recurse down the tree and rebalance on the way up. -/
def insertFixup (x : Nat) : OSRBTree → OSRBTree
  | empty => mk Color.red empty x empty
  | node c l y s r =>
      if x < y then
        if c = Color.black then balanceLeft (insertFixup x l) y r
        else mk Color.red (insertFixup x l) y r
      else if x > y then
        if c = Color.black then balanceRight l y (insertFixup x r)
        else mk Color.red l y (insertFixup x r)
      else node c l y s r

/-- Insert a key into an augmented red-black tree and repaint the root black. -/
def insert (x : Nat) (t : OSRBTree) : OSRBTree :=
  repaintBlack (insertFixup x t)

/-! ### The augmentation invariant survives balancing -/

/-- Repainting the root black preserves the size augmentation invariant. -/
theorem wellSized_repaintBlack {t : OSRBTree} (h : WellSized t) :
    WellSized (repaintBlack t) := by
  cases t with
  | empty => trivial
  | node c l k s r => exact ⟨h.1, h.2.1, h.2.2⟩

/-- {lit}`balanceLeft` preserves the size augmentation invariant. -/
theorem wellSized_balanceLeft {l : OSRBTree} {y : Nat} {r : OSRBTree}
    (hl : WellSized l) (hr : WellSized r) :
    WellSized (balanceLeft l y r) := by
  unfold balanceLeft
  split
  · obtain ⟨⟨ha, hb, _⟩, hc, _⟩ := hl
    exact wellSized_mk (wellSized_mk ha hb) (wellSized_mk hc hr)
  · obtain ⟨ha, ⟨hb, hc, _⟩, _⟩ := hl
    exact wellSized_mk (wellSized_mk ha hb) (wellSized_mk hc hr)
  · exact wellSized_mk hl hr

/-- {lit}`balanceRight` preserves the size augmentation invariant. -/
theorem wellSized_balanceRight {l : OSRBTree} {y : Nat} {r : OSRBTree}
    (hl : WellSized l) (hr : WellSized r) :
    WellSized (balanceRight l y r) := by
  unfold balanceRight
  split
  · obtain ⟨⟨hb, hc, _⟩, hd, _⟩ := hr
    exact wellSized_mk (wellSized_mk hl hb) (wellSized_mk hc hd)
  · obtain ⟨hb, ⟨hc, hd, _⟩, _⟩ := hr
    exact wellSized_mk (wellSized_mk hl hb) (wellSized_mk hc hd)
  · exact wellSized_mk hl hr

/-- {lit}`insertFixup` preserves the size augmentation invariant. -/
theorem wellSized_insertFixup (x : Nat) {t : OSRBTree} (h : WellSized t) :
    WellSized (insertFixup x t) := by
  induction t with
  | empty =>
      simp only [insertFixup]
      exact wellSized_mk (by trivial) (by trivial)
  | node c l y s r ihl ihr =>
      have hl : WellSized l := h.1
      have hr : WellSized r := h.2.1
      simp only [insertFixup]
      by_cases h1 : x < y
      · simp only [h1, if_true]
        by_cases hc : c = Color.black
        · simp only [hc, if_true]
          exact wellSized_balanceLeft (ihl hl) hr
        · simp only [hc, if_false]
          exact wellSized_mk (ihl hl) hr
      · simp only [h1, if_false]
        by_cases h2 : x > y
        · simp only [h2, if_true]
          by_cases hc : c = Color.black
          · simp only [hc, if_true]
            exact wellSized_balanceRight hl (ihr hr)
          · simp only [hc, if_false]
            exact wellSized_mk hl (ihr hr)
        · simp only [h2, if_false]
          exact h

/--
**Augmentation invariant through executable insertion (CLRS 14.1 through
`RB-INSERT`).**  Inserting a key into a well-sized augmented red-black tree
produces a well-sized tree: every cached subtree-size field remains correct
after the red-black rebalancing (CLRS 14.1 maintained through {lit}`insert`).
-/
theorem wellSized_insert (x : Nat) {t : OSRBTree} (h : WellSized t) :
    WellSized (insert x t) := by
  unfold insert
  exact wellSized_repaintBlack (wellSized_insertFixup x h)

/-- After insertion the cached root size equals the mathematical subtree size. -/
theorem storedSize_insert (x : Nat) {t : OSRBTree} (h : WellSized t) :
    storedSize (insert x t) = realSize (insert x t) :=
  storedSize_eq_realSize_of_wellSized (wellSized_insert x h)

/--
After insertion the augmented (cached-size) selector still implements the ideal
recomputed-size rank selector.
-/
theorem osSelect?_insert_eq_rankSelect? (x : Nat) {t : OSRBTree}
    (h : WellSized t) (i : Nat) :
    osSelect? (insert x t) i = rankSelect? (insert x t) i :=
  osSelect?_eq_rankSelect?_of_wellSized (wellSized_insert x h)

/-! ### Refinement onto the executable Chapter 13 red-black insertion -/

/-- Erasing the size field commutes with repainting the root black. -/
theorem toRB_repaintBlack (t : OSRBTree) :
    toRB (repaintBlack t) = RBTree.repaintRoot Color.black (toRB t) := by
  cases t with
  | empty => rfl
  | node c l k s r => rfl

/-- Erasing the size field commutes with {lit}`balanceLeft`. -/
theorem toRB_balanceLeft (l : OSRBTree) (y : Nat) (r : OSRBTree) :
    toRB (balanceLeft l y r) = RBTree.balanceLeft (toRB l) y (toRB r) := by
  cases l with
  | empty => rfl
  | node c a w s b =>
    cases c with
    | black => rfl
    | red =>
      cases a with
      | empty =>
          cases b with
          | empty => rfl
          | node cb bl bk bs br => cases cb <;> rfl
      | node ca al ak as' ar =>
          cases ca with
          | red => rfl
          | black =>
              cases b with
              | empty => rfl
              | node cb bl bk bs br => cases cb <;> rfl

/-- Erasing the size field commutes with {lit}`balanceRight`. -/
theorem toRB_balanceRight (l : OSRBTree) (y : Nat) (r : OSRBTree) :
    toRB (balanceRight l y r) = RBTree.balanceRight (toRB l) y (toRB r) := by
  cases r with
  | empty => rfl
  | node c a w s b =>
    cases c with
    | black => rfl
    | red =>
      cases a with
      | empty =>
          cases b with
          | empty => rfl
          | node cb bl bk bs br => cases cb <;> rfl
      | node ca al ak as' ar =>
          cases ca with
          | red => rfl
          | black =>
              cases b with
              | empty => rfl
              | node cb bl bk bs br => cases cb <;> rfl

/-- Erasing the size field commutes with {lit}`insertFixup`. -/
theorem toRB_insertFixup (x : Nat) (t : OSRBTree) :
    toRB (insertFixup x t) = RBTree.insertFixup x (toRB t) := by
  induction t with
  | empty => rfl
  | node c l y s r ihl ihr =>
      simp only [insertFixup, RBTree.insertFixup, toRB, apply_ite toRB, toRB_mk,
        toRB_balanceLeft, toRB_balanceRight, ihl, ihr]

/--
**Refinement.**  The augmented insertion refines the *executable* Chapter 13
red-black insertion: erasing the cached size fields turns
{lit}`OSRBTree.insert` into {lit}`CLRS.Chapter13.RBTree.insert`.
-/
theorem toRB_insert (x : Nat) (t : OSRBTree) :
    toRB (insert x t) = RBTree.insert x (toRB t) := by
  unfold insert RBTree.insert
  rw [toRB_repaintBlack, toRB_insertFixup]

/--
Through the refinement, the Chapter 13 red-black shape invariant is maintained by
the augmented insertion.
-/
theorem redBlackShape_toRB_insert (x : Nat) {t : OSRBTree}
    (h : RBTree.RedBlackShape (toRB t)) :
    RBTree.RedBlackShape (toRB (insert x t)) := by
  rw [toRB_insert]
  exact RBTree.redBlackShape_insert h

/-- Through the refinement, insertion preserves membership (as an inorder key). -/
theorem mem_keys_insert (x y : Nat) (t : OSRBTree) :
    y ∈ keys (insert x t) ↔ y = x ∨ y ∈ keys t := by
  simp only [← inTree_toRB, toRB_insert, RBTree.inTree_insert_iff]

end OSRBTree

end Chapter14
end CLRS
