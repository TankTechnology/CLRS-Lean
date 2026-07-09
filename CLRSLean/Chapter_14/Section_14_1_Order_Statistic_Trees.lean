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

**Bridge to Chapter 13 red-black balancing:**

* Theorem {lit}`rbInsert_wellSized`: inserting a key into a well-sized OST via
  the red-black insertion algorithm, then recomputing cached sizes, yields a
  well-sized OST.
* Theorem {lit}`osSelect?_rbInsert_eq_rankSelect?_rbInsert`: after red-black
  insertion and size recomputation, the augmented selector agrees with the
  ideal rank selector on the resulting tree.
* Theorem {lit}`inTree_rbInsert_new_key`: after red-black insertion and size
  recomputation, the new key is present in the underlying RBT projection.
* Theorem {lit}`realSize_ofRBTree_toRBTree`: the mathematical subtree size is
  preserved by the round-trip conversion through {lit}`toRBTree` and
  {lit}`ofRBTree`.
* Theorem {lit}`recomputeSizes_ofRBTree_toRBTree_of_wellSized`: recomputing
  sizes after the round-trip conversion recovers the original well-sized tree
  exactly.

Current gaps:

* Interval trees and the general augmentation theorem remain future targets.
* Red-black deletion with size-augmentation maintenance is not yet covered.
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

/-! ## Bridge to Chapter 13 red-black balancing -/

/-- The inorder key sequence of a red-black tree, ignoring colors. -/
def inorderKeys (t : Chapter13.RBTree) : List Nat :=
  match t with
  | Chapter13.RBTree.empty => []
  | Chapter13.RBTree.node _ left key right =>
      inorderKeys left ++ [key] ++ inorderKeys right

/-- Project an order-statistic tree onto a red-black tree by forgetting cached
sizes and assigning all nodes the color black. -/
def toRBTree : OSTree → Chapter13.RBTree
  | empty => Chapter13.RBTree.empty
  | node left key _size right =>
      Chapter13.RBTree.node Chapter13.Color.black (toRBTree left) key
        (toRBTree right)

/-- Embed a red-black tree into an order-statistic tree by forgetting colors and
setting all cached sizes to zero. -/
def ofRBTree : Chapter13.RBTree → OSTree
  | Chapter13.RBTree.empty => empty
  | Chapter13.RBTree.node _color left key right =>
      node (ofRBTree left) key 0 (ofRBTree right)

/-- The inorder keys of an RBTree embedding match the original RBTree keys. -/
theorem keys_ofRBTree (t : Chapter13.RBTree) :
    keys (ofRBTree t) = inorderKeys t := by
  induction t with
  | empty => rfl
  | node _ left key right ihLeft ihRight =>
      simp [ofRBTree, keys, inorderKeys, ihLeft, ihRight]

/-- The inorder keys of an OSTree projection match the original OSTree keys. -/
theorem inorderKeys_toRBTree (t : OSTree) :
    inorderKeys (toRBTree t) = keys t := by
  induction t with
  | empty => rfl
  | node left key size right ihLeft ihRight =>
      simp [toRBTree, keys, inorderKeys, ihLeft, ihRight]

/-- The mathematical subtree size is preserved by the toRBTree/ofRBTree
round-trip. -/
theorem realSize_ofRBTree_toRBTree (t : OSTree) :
    realSize (ofRBTree (toRBTree t)) = realSize t := by
  induction t with
  | empty => rfl
  | node left key size right ihLeft ihRight =>
      simp [ofRBTree, toRBTree, realSize, ihLeft, ihRight]

/-- Recomputing sizes after the toRBTree/ofRBTree round-trip recovers the
original well-sized tree exactly. -/
theorem recomputeSizes_ofRBTree_toRBTree_of_wellSized {t : OSTree}
    (h : WellSized t) : recomputeSizes (ofRBTree (toRBTree t)) = t := by
  induction t with
  | empty => rfl
  | node left key size right ihLeft ihRight =>
      rcases h with ⟨hLeft, hRight, hSize⟩
      have ihL := ihLeft hLeft
      have ihR := ihRight hRight
      simp [recomputeSizes, ofRBTree, toRBTree, ihL, ihR]
      rw [hSize]

/-- Inserting a key into a well-sized order-statistic tree via the red-black
insertion algorithm and then recomputing the cached sizes yields a well-sized
order-statistic tree.

This theorem bridges the OST size augmentation (Section 14.1) to the RBT
insertion algorithm (Section 13.1): it says that if we start with a well-sized
OST, package its structure as an RBT, insert a key using the provably
shape-preserving {lit}`Chapter13.RBTree.insert`, convert back to an OST, and
recompute sizes, we obtain a well-sized OST. -/
theorem rbInsert_wellSized {t : OSTree} (_h : WellSized t) (x : Nat) :
    WellSized
      (recomputeSizes (ofRBTree (Chapter13.RBTree.insert x (toRBTree t)))) :=
  recomputeSizes_wellSized _

/-- After red-black insertion and size recomputation, the augmented order-
statistic selector agrees with the ideal rank selector on the resulting tree. -/
theorem osSelect?_rbInsert_eq_rankSelect?_rbInsert (t : OSTree) (x i : Nat) :
    osSelect?
      (recomputeSizes (ofRBTree (Chapter13.RBTree.insert x (toRBTree t)))) i =
    rankSelect?
      (recomputeSizes (ofRBTree (Chapter13.RBTree.insert x (toRBTree t)))) i :=
  osSelect?_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized _)

/-- Projecting through recomputeSizes preserves the RBTree structure. -/
theorem toRBTree_recomputeSizes (t : OSTree) :
    toRBTree (recomputeSizes t) = toRBTree t := by
  induction t with
  | empty => rfl
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, toRBTree, ihLeft, ihRight]

/-- Membership in the double projection is equivalent to membership in the
original RBTree. -/
theorem inTree_toRBTree_ofRBTree (x : Nat) (t : Chapter13.RBTree) :
    Chapter13.RBTree.InTree x (toRBTree (ofRBTree t)) ↔
      Chapter13.RBTree.InTree x t := by
  induction t with
  | empty => simp [toRBTree, ofRBTree, Chapter13.RBTree.InTree]
  | node _ left key right ihLeft ihRight =>
      simp [toRBTree, ofRBTree, Chapter13.RBTree.InTree, ihLeft, ihRight]

/-- The RBT insertion membership guarantee lifts to the OST embedding: after
red-black insertion and size recomputation, the new key is present in the tree
according to the {lit}`Chapter13.RBTree.InTree` predicate on the underlying
RBT projection. -/
theorem inTree_rbInsert_new_key (t : OSTree) (x : Nat) :
    Chapter13.RBTree.InTree x
      (toRBTree
        (recomputeSizes (ofRBTree (Chapter13.RBTree.insert x (toRBTree t))))) := by
  -- The RBT insertion theorem guarantees the new key is in the result.
  have h_insert : Chapter13.RBTree.InTree x
      (Chapter13.RBTree.insert x (toRBTree t)) := by
    rw [Chapter13.RBTree.inTree_insert_iff]
    exact Or.inl rfl
  -- recomputeSizes doesn't change the RBTree projection.
  rw [toRBTree_recomputeSizes]
  -- The double projection preserves membership.
  rw [inTree_toRBTree_ofRBTree]
  exact h_insert

end OSTree

end Chapter14
end CLRS
