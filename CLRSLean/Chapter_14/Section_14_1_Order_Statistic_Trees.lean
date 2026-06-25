import Mathlib

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
* Theorem {lit}`recomputeSizes_wellSized`: recomputing size fields establishes
  the augmentation invariant.
* Theorem {lit}`keys_recomputeSizes`: recomputing size fields preserves the
  inorder key sequence.
* Theorem {lit}`osSelect?_eq_rankSelect?_of_wellSized`: on a well-sized tree,
  the augmented selector agrees with the ideal rank selector.

Current gaps:

* This file does not yet combine the size augmentation with red-black rotations.
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

/-- Recomputing cached size fields establishes the size augmentation invariant. -/
theorem recomputeSizes_wellSized (t : OSTree) :
    WellSized (recomputeSizes t) := by
  induction t with
  | empty =>
      trivial
  | node left key size right ihLeft ihRight =>
      simp [recomputeSizes, WellSized, ihLeft, ihRight]

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

/--
Recomputing size fields makes the augmented selector agree with the ideal
selector without requiring an external invariant proof.
-/
theorem osSelect?_recomputeSizes_eq_rankSelect? (t : OSTree) (i : Nat) :
    osSelect? (recomputeSizes t) i = rankSelect? (recomputeSizes t) i := by
  exact osSelect?_eq_rankSelect?_of_wellSized (recomputeSizes_wellSized t)

end OSTree

end Chapter14
end CLRS
