import Mathlib
import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-! # Section 14.3 - Interval trees

This file formalizes the second classic augmentation from CLRS Chapter 14:
interval trees.  Each node stores an interval and a cached maximum high endpoint
of its subtree.  The search algorithm uses the cached maximum to prune the left
subtree when no overlap is possible there.

To make the pattern reusable, we first define a small generic augmentation
framework: an {lit}`AugmentedTree α β` carries a value of type {lit}`α` at each node and
a cached augmentation of type {lit}`β`.  An {lit}`Augmentation α β` provides the empty
default and the local recombination function.  The framework proves that
recomputing the augmentation from the children preserves the {lit}`WellAugmented`
invariant, and that rotations preserve the inorder key sequence and the
{lit}`WellAugmented` invariant for augmentations whose combine operator behaves like
{lit}`max` (which is the case for the interval-tree instantiation).  We then
instantiate it to interval trees with the max-high augmentation, and show that
the executable {lit}`intervalSearch?` is correct on well-augmented BSTs.

Main results:

* Generic {lit}`AugmentedTree` lemmas: {lit}`keys_recompute`, {lit}`realAug_recompute`,
  {lit}`recompute_wellAugmented`, {lit}`rotateLeft_wellAugmented`,
  {lit}`rotateRight_wellAugmented`.
* Interval-tree correctness: {lit}`intervalSearch?_some_overlap` and
  {lit}`intervalSearch?_none_noOverlap` (combined as {lit}`intervalSearch?_spec`).
* General augmentation theorem (CLRS Theorem 14.1): {lit}`augmentation_theorem`
  packages that rotations, recomputation, and generic BST {lit}`insert` maintain
  the {lit}`WellAugmented` invariant and the semantic augmentation for any
  rotation-invariant augmentation.
* Size augmentation instance: {lit}`sizeAug` with {lit}`realAug_sizeAug_eq_length`,
  showing order-statistic size caching is an instance of the same framework.
* Red-black bridge: {lit}`rb_augmentation_bridge` shows Chapter 13's red-black
  rotations and root recoloring preserve any rotation-invariant augmentation's
  value (and the inorder key list), so the augmentation is maintainable through
  the red-black operations.
* General augmentation interface: {lit}`AugmentedRBTree` threads an **arbitrary**
  {lit}`Augmentation` through an *executable* red-black insertion; its smart
  constructor {lit}`AugmentedRBTree.mk` recomputes the cached value, so
  {lit}`AugmentedRBTree.wellAugmented_insert` shows the invariant survives
  balancing and {lit}`AugmentedRBTree.toRB_insert` shows the augmentation-erasing
  projection refines Chapter 13's executable {lit}`RBTree.insert`.  Both the size
  and interval instances are recovered from it
  ({lit}`AugmentedRBTree.sizeAug_wellAugmented_insert`,
  {lit}`AugmentedRBTree.maxHighAug_wellAugmented_insert`).

Status: {lit}`proved` for the interval-tree augmentation framework, the general
augmentation theorem, the red-black rotation bridge, and the general executable
augmentation interface (an arbitrary augmentation threaded through an executable
red-black insertion, refining Chapter 13's {lit}`RBTree.insert`).

Deferred refinements: monoid-based augmentation, and threading an augmentation
through executable red-black *deletion* (blocked on the Chapter 13 executable
delete loop).  The stored-augmentation-field refinement through executable
{lit}`RBTree.insert` is now proved generically.
-/

namespace CLRS
namespace Chapter14

/-! ## Generic augmented trees -/

/-- An augmentation schema for a binary tree: a default for the empty tree and
a local recombination function. -/
structure Augmentation (α β : Type) [Inhabited β] where
  base : β
  combine : α → β → β → β

/-- Typeclass asserting that an augmentation's {lit}`combine` operation satisfies the
rotation-invariance law required for BST rotations to preserve the cached
augmentation.  The max-high augmentation is the motivating example. -/
class IsRotationInvariant {α β : Type} [Inhabited β] (aug : Augmentation α β) : Prop where
  combine_rotate :
    ∀ (x y : α) (a b c : β),
      aug.combine y (aug.combine x a b) c = aug.combine x a (aug.combine y b c)

/-- A binary tree whose internal nodes cache an augmentation value. -/
inductive AugmentedTree (α β : Type) where
  | empty : AugmentedTree α β
  | node : AugmentedTree α β → α → β → AugmentedTree α β → AugmentedTree α β
  deriving Repr, DecidableEq

namespace AugmentedTree

variable {α β : Type} [Inhabited β] (aug : Augmentation α β)

/-- Inorder traversal of the stored values. -/
@[simp]
def keys : AugmentedTree α β → List α
  | empty => []
  | node left key _ right => keys left ++ [key] ++ keys right

/-- The cached augmentation at the root. -/
@[simp]
def storedAug : AugmentedTree α β → β
  | empty => aug.base
  | node _ _ a _ => a

/-- The mathematically correct augmentation computed from the children. -/
@[simp]
def realAug : AugmentedTree α β → β
  | empty => aug.base
  | node left key _ right => aug.combine key (realAug left) (realAug right)

/-- Every cached augmentation agrees with the mathematically correct one. -/
@[simp]
def WellAugmented : AugmentedTree α β → Prop
  | empty => True
  | node left key a right =>
      WellAugmented left ∧ WellAugmented right ∧
      a = realAug aug (node left key a right)

/-- Recompute every cached augmentation from the children upward. -/
@[simp]
def recompute : AugmentedTree α β → AugmentedTree α β
  | empty => empty
  | node left key _ right =>
      let left' := recompute left
      let right' := recompute right
      node left' key (aug.combine key (realAug aug left') (realAug aug right')) right'

/-- Left rotation with local augmentation recomputation. -/
@[simp]
def rotateLeft : AugmentedTree α β → AugmentedTree α β
  | node a x _ (node b y _ c) =>
      let left' := node a x (aug.combine x (realAug aug a) (realAug aug b)) b
      node left' y (aug.combine y (realAug aug left') (realAug aug c)) c
  | t => t

/-- Right rotation with local augmentation recomputation. -/
@[simp]
def rotateRight : AugmentedTree α β → AugmentedTree α β
  | node (node a x _ b) y _ c =>
      let right' := node b y (aug.combine y (realAug aug b) (realAug aug c)) c
      node a x (aug.combine x (realAug aug a) (realAug aug right')) right'
  | t => t

/-- Recomputing preserves the inorder key sequence. -/
theorem keys_recompute (t : AugmentedTree α β) :
    keys (recompute aug t) = keys t := by
  induction t with
  | empty => rfl
  | node left key _ right ihLeft ihRight =>
      simp [recompute, keys, ihLeft, ihRight]

/-- Recomputing preserves the mathematical augmentation. -/
theorem realAug_recompute (t : AugmentedTree α β) :
    realAug aug (recompute aug t) = realAug aug t := by
  induction t with
  | empty => rfl
  | node left key _ right ihLeft ihRight =>
      simp [recompute, realAug, ihLeft, ihRight]

/-- Recomputing establishes the well-augmented invariant. -/
theorem recompute_wellAugmented (t : AugmentedTree α β) :
    WellAugmented aug (recompute aug t) := by
  induction t with
  | empty => trivial
  | node left key _ right ihLeft ihRight =>
      simp [recompute, WellAugmented, realAug_recompute, ihLeft, ihRight]

/-- A well-augmented tree has a correct root augmentation. -/
theorem storedAug_eq_realAug_of_wellAugmented {t : AugmentedTree α β}
    (h : WellAugmented aug t) :
    storedAug aug t = realAug aug t := by
  cases t with
  | empty => rfl
  | node left key a right =>
      exact h.2.2

/-- Left rotation preserves the inorder key sequence. -/
theorem keys_rotateLeft (t : AugmentedTree α β) :
    keys (rotateLeft aug t) = keys t := by
  cases t with
  | empty => rfl
  | node a x _ right =>
      cases right with
      | empty => rfl
      | node b y _ c =>
          simp [rotateLeft, keys, List.append_assoc]

/-- Right rotation preserves the inorder key sequence. -/
theorem keys_rotateRight (t : AugmentedTree α β) :
    keys (rotateRight aug t) = keys t := by
  cases t with
  | empty => rfl
  | node left y _ c =>
      cases left with
      | empty => rfl
      | node a x _ b =>
          simp [rotateRight, keys, List.append_assoc]

/-- Left rotation preserves the mathematical augmentation. -/
theorem realAug_rotateLeft (t : AugmentedTree α β) [IsRotationInvariant aug] :
    realAug aug (rotateLeft aug t) = realAug aug t := by
  cases t with
  | empty => rfl
  | node a x _ right =>
      cases right with
      | empty => rfl
      | node b y _ c =>
          simp [rotateLeft, realAug]
          rw [IsRotationInvariant.combine_rotate]

/-- Right rotation preserves the mathematical augmentation. -/
theorem realAug_rotateRight (t : AugmentedTree α β) [IsRotationInvariant aug] :
    realAug aug (rotateRight aug t) = realAug aug t := by
  cases t with
  | empty => rfl
  | node left y _ c =>
      cases left with
      | empty => rfl
      | node a x _ b =>
          simp [rotateRight, realAug]
          rw [IsRotationInvariant.combine_rotate]

/-- Left rotation preserves the cached root augmentation of a well-augmented tree. -/
theorem storedAug_rotateLeft_of_wellAugmented {t : AugmentedTree α β}
    [IsRotationInvariant aug] (h : WellAugmented aug t) :
    storedAug aug (rotateLeft aug t) = storedAug aug t := by
  cases t with
  | empty => rfl
  | node a x _ right =>
      cases right with
      | empty => rfl
      | node b y _ c =>
          rcases h with ⟨_ha, hRight, hSize⟩
          simp [rotateLeft, storedAug, realAug, hSize]
          rw [IsRotationInvariant.combine_rotate]

/-- Right rotation preserves the cached root augmentation of a well-augmented tree. -/
theorem storedAug_rotateRight_of_wellAugmented {t : AugmentedTree α β}
    [IsRotationInvariant aug] (h : WellAugmented aug t) :
    storedAug aug (rotateRight aug t) = storedAug aug t := by
  cases t with
  | empty => rfl
  | node left y _ c =>
      cases left with
      | empty => rfl
      | node a x _ b =>
          rcases h with ⟨hLeft, _hc, hSize⟩
          simp [rotateRight, storedAug, realAug, hSize]
          rw [IsRotationInvariant.combine_rotate]

/-- Left rotation preserves the well-augmented invariant. -/
theorem rotateLeft_wellAugmented {t : AugmentedTree α β}
    (h : WellAugmented aug t) :
    WellAugmented aug (rotateLeft aug t) := by
  cases t with
  | empty => exact h
  | node a x _ right =>
      cases right with
      | empty => simpa [rotateLeft] using h
      | node b y _ c =>
          rcases h with ⟨ha, hRight, hSize⟩
          rcases hRight with ⟨hb, hc, hRightSize⟩
          simp [rotateLeft, WellAugmented, realAug, ha, hb, hc]

/-- Right rotation preserves the well-augmented invariant. -/
theorem rotateRight_wellAugmented {t : AugmentedTree α β}
    (h : WellAugmented aug t) :
    WellAugmented aug (rotateRight aug t) := by
  cases t with
  | empty => exact h
  | node left y _ c =>
      cases left with
      | empty => simpa [rotateRight] using h
      | node a x _ b =>
          rcases h with ⟨hLeft, hc, hSize⟩
          rcases hLeft with ⟨ha, hb, hLeftSize⟩
          simp [rotateRight, WellAugmented, realAug, ha, hb, hc]

/-! ### Generic BST insertion and the general augmentation theorem (CLRS 14.1) -/

/-- BST insertion by a Boolean comparison {lit}`lt`, recomputing the cached
augmentation locally at each node.  Generic over any augmentation. -/
def insert (lt : α → α → Bool) (x : α) : AugmentedTree α β → AugmentedTree α β
  | empty => node empty x (aug.combine x aug.base aug.base) empty
  | node l k _ r =>
      if lt x k then
        let l' := insert lt x l
        node l' k (aug.combine k (realAug aug l') (realAug aug r)) r
      else if lt k x then
        let r' := insert lt x r
        node l k (aug.combine k (realAug aug l) (realAug aug r')) r'
      else
        node l k (aug.combine k (realAug aug l) (realAug aug r)) r

/-- Insertion adds exactly the inserted key to the inorder key multiset. -/
theorem mem_keys_insert (lt : α → α → Bool) (x y : α) (t : AugmentedTree α β) :
    y ∈ keys (insert aug lt x t) → y = x ∨ y ∈ keys t := by
  induction t with
  | empty => simp [insert, keys]
  | node l k a r ihl ihr =>
      simp only [insert]
      split
      · simp only [keys, List.mem_append, List.mem_singleton]
        rintro ((h | h) | h)
        · rcases ihl h with h' | h' <;> tauto
        · tauto
        · tauto
      · split
        · simp only [keys, List.mem_append, List.mem_singleton]
          rintro ((h | h) | h)
          · tauto
          · tauto
          · rcases ihr h with h' | h' <;> tauto
        · simp only [keys, List.mem_append, List.mem_singleton]
          tauto

/-- Generic insertion preserves the well-augmented invariant. -/
theorem insert_wellAugmented (lt : α → α → Bool) (x : α) {t : AugmentedTree α β}
    (h : WellAugmented aug t) : WellAugmented aug (insert aug lt x t) := by
  induction t with
  | empty => simp [insert, WellAugmented, realAug]
  | node l k a r ihl ihr =>
      rcases h with ⟨hl, hr, _ha⟩
      simp only [insert]
      split
      · exact ⟨ihl hl, hr, by simp [realAug]⟩
      · split
        · exact ⟨hl, ihr hr, by simp [realAug]⟩
        · exact ⟨hl, hr, by simp [realAug]⟩

/-- **CLRS Theorem 14.1 (maintainability of augmentations).**  For any
locally-computable, rotation-invariant augmentation, every structural primitive
used by red-black insertion and deletion — left and right rotation, subtree
recomputation, and BST insertion — preserves the inorder key sequence and the
mathematical augmentation, and preserves (or re-establishes) the
{lit}`WellAugmented` invariant.  Hence the augmentation can be maintained through the
red-black operations. -/
theorem augmentation_theorem [IsRotationInvariant aug] :
    (∀ t : AugmentedTree α β, WellAugmented aug t → WellAugmented aug (rotateLeft aug t)) ∧
    (∀ t : AugmentedTree α β, WellAugmented aug t → WellAugmented aug (rotateRight aug t)) ∧
    (∀ t : AugmentedTree α β, keys (rotateLeft aug t) = keys t) ∧
    (∀ t : AugmentedTree α β, keys (rotateRight aug t) = keys t) ∧
    (∀ t : AugmentedTree α β, realAug aug (rotateLeft aug t) = realAug aug t) ∧
    (∀ t : AugmentedTree α β, realAug aug (rotateRight aug t) = realAug aug t) ∧
    (∀ t : AugmentedTree α β, WellAugmented aug (recompute aug t)) ∧
    (∀ (lt : α → α → Bool) (x : α) (t : AugmentedTree α β),
        WellAugmented aug t → WellAugmented aug (insert aug lt x t)) :=
  ⟨fun _ h => rotateLeft_wellAugmented aug h,
   fun _ h => rotateRight_wellAugmented aug h,
   fun t => keys_rotateLeft aug t,
   fun t => keys_rotateRight aug t,
   fun t => realAug_rotateLeft aug t,
   fun t => realAug_rotateRight aug t,
   fun t => recompute_wellAugmented aug t,
   fun lt x _ h => insert_wellAugmented aug lt x h⟩

end AugmentedTree

/-! ## Size augmentation (order-statistic trees as an instance)

The order-statistic augmentation of Section 14.1 — caching each subtree's node
count — is an instance of the same generic framework, demonstrating CLRS
Theorem 14.1 for a second concrete field alongside interval trees' max-high. -/

/-- The subtree-size augmentation: the cached value is the number of nodes. -/
def sizeAug (α : Type) : Augmentation α Nat := ⟨0, fun _ l r => 1 + l + r⟩

instance (α : Type) : IsRotationInvariant (sizeAug α) where
  combine_rotate x y a b c := by simp [sizeAug]; omega

/-- The size augmentation's mathematical value is exactly the node count. -/
theorem realAug_sizeAug_eq_length {α : Type} (t : AugmentedTree α Nat) :
    AugmentedTree.realAug (sizeAug α) t = (AugmentedTree.keys t).length := by
  induction t with
  | empty => rfl
  | node l k a r ihl ihr =>
      simp only [AugmentedTree.realAug]
      rw [ihl, ihr]
      simp only [sizeAug, AugmentedTree.keys,
        List.length_append, List.length_cons, List.length_nil]
      omega

/-! # Interval trees -/

/-- A closed interval of natural numbers. -/
def Interval := Nat × Nat

def Interval.low (i : Interval) : Nat := i.1
def Interval.high (i : Interval) : Nat := i.2

def Interval.overlaps (i j : Interval) : Bool :=
  i.low ≤ j.high && j.low ≤ i.high

@[simp]
theorem Interval.overlaps_iff {i j : Interval} :
    Interval.overlaps i j = true ↔ i.low ≤ j.high ∧ j.low ≤ i.high := by
  simp [Interval.overlaps]

/-- Interval trees are augmented trees whose node value is an interval and whose
augmentation is the maximum high endpoint in the subtree. -/
abbrev IntervalTree := AugmentedTree Interval Nat

def IntervalTree.maxHighAug : Augmentation Interval Nat :=
  ⟨0, fun i l r => max i.high (max l r)⟩

instance : IsRotationInvariant IntervalTree.maxHighAug where
  combine_rotate x y a b c := by
    simp [IntervalTree.maxHighAug]
    ac_rfl

namespace IntervalTree

/-- Inorder list of intervals. -/
def keys : IntervalTree → List Interval :=
  AugmentedTree.keys

/-- Cached maximum high endpoint at the root. -/
def storedMaxHigh : IntervalTree → Nat :=
  AugmentedTree.storedAug maxHighAug

/-- Mathematical maximum high endpoint in the subtree. -/
def realMaxHigh : IntervalTree → Nat :=
  AugmentedTree.realAug maxHighAug

/-- The max-high augmentation invariant. -/
def WellAugmented : IntervalTree → Prop :=
  AugmentedTree.WellAugmented maxHighAug

/-- Recompute every cached max-high field. -/
def recompute : IntervalTree → IntervalTree :=
  AugmentedTree.recompute maxHighAug

/-- Left rotation with local max-high recomputation. -/
def rotateLeft : IntervalTree → IntervalTree :=
  AugmentedTree.rotateLeft maxHighAug

/-- Right rotation with local max-high recomputation. -/
def rotateRight : IntervalTree → IntervalTree :=
  AugmentedTree.rotateRight maxHighAug

/-- Every interval in the tree has low endpoint at most {lit}`x`. -/
def allLowLE (t : IntervalTree) (x : Nat) : Prop :=
  ∀ i ∈ keys t, i.low ≤ x

/-- Every interval in the tree has low endpoint at least {lit}`x`. -/
def allLowGE (t : IntervalTree) (x : Nat) : Prop :=
  ∀ i ∈ keys t, x ≤ i.low

/-- Binary-search-tree ordering by interval low endpoint. -/
def IsBST : IntervalTree → Prop
  | AugmentedTree.empty => True
  | AugmentedTree.node left int _ right =>
      IsBST left ∧ IsBST right ∧
      allLowLE left int.low ∧ allLowGE right int.low

/-- Boolean emptiness test for interval trees. -/
def isEmpty : IntervalTree → Bool
  | AugmentedTree.empty => true
  | AugmentedTree.node _ _ _ _ => false

/-- Decision to recurse into the left subtree during interval search. -/
def goLeft (left : IntervalTree) (q : Interval) : Bool :=
  !isEmpty left && decide (storedMaxHigh left ≥ q.low)

/-- The executable interval-search algorithm from CLRS. -/
def intervalSearch? : IntervalTree → Interval → Option Interval
  | AugmentedTree.empty, _ => none
  | AugmentedTree.node left int _ right, q =>
      if Interval.overlaps int q then
        some int
      else if goLeft left q then
        intervalSearch? left q
      else
        intervalSearch? right q

/-- Does the tree contain an interval overlapping the query? -/
def hasOverlap (t : IntervalTree) (q : Interval) : Prop :=
  ∃ i ∈ keys t, Interval.overlaps i q

end IntervalTree

namespace IntervalTree

@[simp]
theorem keys_empty : keys AugmentedTree.empty = [] := by
  simp [keys]

@[simp]
theorem keys_node {left right : IntervalTree} {int : Interval} {mx : Nat} :
    keys (AugmentedTree.node left int mx right) = keys left ++ [int] ++ keys right := by
  simp [keys]

@[simp]
theorem isEmpty_empty : isEmpty AugmentedTree.empty = true := by rfl

@[simp]
theorem isEmpty_node {left right : IntervalTree} {int : Interval} {mx : Nat} :
    isEmpty (AugmentedTree.node left int mx right) = false := by rfl

/-- A true {lit}`goLeft` condition means the left subtree is non-empty and its max-high
is at least the query low. -/
theorem goLeft_true {left : IntervalTree} {q : Interval}
    (h : goLeft left q = true) :
    left ≠ AugmentedTree.empty ∧ storedMaxHigh left ≥ q.low := by
  simp [goLeft, Bool.and_eq_true] at h
  rcases h with ⟨hne, hmax⟩
  constructor
  · cases left with
    | empty => simp at hne
    | node => simp
  · exact hmax

/-- A false {lit}`goLeft` condition means the left subtree is empty or its max-high is
below the query low. -/
theorem goLeft_false {left : IntervalTree} {q : Interval}
    (h : goLeft left q = false) :
    left = AugmentedTree.empty ∨ storedMaxHigh left < q.low := by
  simp [goLeft] at h
  cases left with
  | empty => left; rfl
  | node left int mx right =>
      right
      have hmax : decide (storedMaxHigh (AugmentedTree.node left int mx right) ≥ q.low) = false := by
        simpa using h
      simpa using hmax

/-- Recomputing cached max-high fields preserves the inorder key sequence. -/
theorem keys_recompute (t : IntervalTree) :
    keys (recompute t) = keys t :=
  AugmentedTree.keys_recompute maxHighAug t

/-- Recomputing cached max-high fields preserves the mathematical max-high. -/
theorem realMaxHigh_recompute (t : IntervalTree) :
    realMaxHigh (recompute t) = realMaxHigh t :=
  AugmentedTree.realAug_recompute maxHighAug t

/-- Recomputing cached max-high fields establishes the augmentation invariant. -/
theorem recompute_wellAugmented (t : IntervalTree) :
    WellAugmented (recompute t) :=
  AugmentedTree.recompute_wellAugmented maxHighAug t

/-- A well-augmented interval tree has a correct root max-high field. -/
theorem storedMaxHigh_eq_realMaxHigh_of_wellAugmented {t : IntervalTree}
    (h : WellAugmented t) :
    storedMaxHigh t = realMaxHigh t :=
  AugmentedTree.storedAug_eq_realAug_of_wellAugmented maxHighAug h

/-- Left rotation preserves the well-augmented invariant. -/
theorem rotateLeft_wellAugmented {t : IntervalTree}
    (h : WellAugmented t) :
    WellAugmented (rotateLeft t) :=
  AugmentedTree.rotateLeft_wellAugmented maxHighAug h

/-- Right rotation preserves the well-augmented invariant. -/
theorem rotateRight_wellAugmented {t : IntervalTree}
    (h : WellAugmented t) :
    WellAugmented (rotateRight t) :=
  AugmentedTree.rotateRight_wellAugmented maxHighAug h

/-- Membership in {lit}`keys` respects the inorder list membership relation. -/
@[simp]
theorem mem_keys {t : IntervalTree} {i : Interval} :
    i ∈ keys t ↔ i ∈ AugmentedTree.keys t := by
  rfl

/-- Every stored high endpoint is bounded by the real max-high. -/
theorem high_le_realMaxHigh {t : IntervalTree} {i : Interval}
    (hi : i ∈ keys t) :
    i.high ≤ realMaxHigh t := by
  induction t with
  | empty =>
      simp [keys] at hi
  | node left int _ right ihLeft ihRight =>
      simp [keys] at hi
      rcases hi with hi | hi | hi
      · exact le_trans (ihLeft hi) (by simp [realMaxHigh, AugmentedTree.realAug, maxHighAug])
      · simp [hi, realMaxHigh, AugmentedTree.realAug, maxHighAug]
      · exact le_trans (ihRight hi) (by simp [realMaxHigh, AugmentedTree.realAug, maxHighAug])

/-- If the mathematical max-high of a subtree is below the query low, the subtree
contains no overlap. -/
theorem noOverlap_of_realMaxHigh_lt {t : IntervalTree} {q : Interval}
    (h : realMaxHigh t < q.low) :
    ¬ ∃ i ∈ keys t, Interval.overlaps i q := by
  rintro ⟨i, hi, hov⟩
  rw [Interval.overlaps_iff] at hov
  have hiHigh := high_le_realMaxHigh hi
  have : q.low ≤ i.high := hov.2
  linarith

/-- A tree whose realMaxHigh is at least a positive bound contains a member whose
high is at least that bound. -/
private theorem exists_mem_high_ge {t : IntervalTree} {x : Nat}
    (hx : x > 0) (h : realMaxHigh t ≥ x) :
    ∃ i ∈ keys t, i.high ≥ x := by
  induction t with
  | empty =>
      simp [realMaxHigh, AugmentedTree.realAug, maxHighAug] at h
      omega
  | node left int _ right ihLeft ihRight =>
      simp [realMaxHigh, AugmentedTree.realAug, maxHighAug] at h
      by_cases hi : int.high ≥ x
      · use int; simp [hi, keys_node]
      · have : realMaxHigh left ≥ x ∨ realMaxHigh right ≥ x := by
          simp [realMaxHigh, maxHighAug] at h ⊢
          omega
        rcases this with h' | h'
        · obtain ⟨k, hk, hkHigh⟩ := ihLeft h'
          use k; simp [hk, hkHigh, keys_node]
        · obtain ⟨k, hk, hkHigh⟩ := ihRight h'
          use k; simp [hk, hkHigh, keys_node]

/-- If the left subtree is non-empty, its max-high is at least the query low, and
the current interval does not overlap, then any overlap in the right subtree
forces an overlap in the left subtree.  This is the key pruning invariant for
interval search. -/
theorem overlap_left_of_right_overlap {left right : IntervalTree} {int q : Interval} (mx : Nat)
    (hB : IsBST (AugmentedTree.node left int mx right))
    (hmax : realMaxHigh left ≥ q.low)
    (hcur : ¬ Interval.overlaps int q)
    (hright : ∃ j ∈ keys right, Interval.overlaps j q) :
    ∃ i ∈ keys left, Interval.overlaps i q := by
  rcases hright with ⟨j, hj, hov⟩
  rw [Interval.overlaps_iff] at hov
  rcases hB with ⟨_hBL, _hBR, hLeftLE, hRightGE⟩
  have h1 : int.low ≤ j.low := hRightGE j hj
  have h2 : j.low ≤ q.high := hov.1
  have h3 : int.low ≤ q.high := by linarith
  have h4 : int.high < q.low := by
    by_contra h'
    have hov : Interval.overlaps int q = true := by
      rw [Interval.overlaps_iff]
      exact ⟨h3, by omega⟩
    exact hcur hov
  have h5 : ∃ i ∈ keys left, i.high ≥ q.low := by
    have hx : q.low > 0 := by omega
    exact exists_mem_high_ge hx hmax
  rcases h5 with ⟨i, hi, hiHigh⟩
  have h6 : i.low ≤ int.low := hLeftLE i hi
  have h7 : i.low ≤ q.high := by linarith
  use i, hi
  rw [Interval.overlaps_iff]
  exact ⟨h7, hiHigh⟩

end IntervalTree

namespace IntervalTree

/-- {lit}`hasOverlap` distributes over a node in the obvious way. -/
@[simp]
theorem hasOverlap_node {left right : IntervalTree} {int : Interval} {mx : Nat} {q : Interval} :
    hasOverlap (AugmentedTree.node left int mx right) q ↔
      Interval.overlaps int q = true ∨ hasOverlap left q ∨ hasOverlap right q := by
  simp [hasOverlap, keys_node, Interval.overlaps_iff]
  constructor
  · rintro ⟨i, (hi | rfl | hi), hlow, hhigh⟩
    · right; left; use i
    · left; exact ⟨hlow, hhigh⟩
    · right; right; use i
  · rintro (⟨hlow, hhigh⟩ | ⟨i, hi, hlow, hhigh⟩ | ⟨i, hi, hlow, hhigh⟩)
    · use int; simp; exact ⟨hlow, hhigh⟩
    · use i; simp [hi]; exact ⟨hlow, hhigh⟩
    · use i; simp [hi]; exact ⟨hlow, hhigh⟩

/-- The executable interval search returns only intervals that are in the tree and
overlap the query. -/
theorem intervalSearch?_some_overlap {t : IntervalTree} (hB : IsBST t) (hW : WellAugmented t)
    (q : Interval) (i : Interval) :
    intervalSearch? t q = some i → i ∈ keys t ∧ Interval.overlaps i q := by
  induction t with
  | empty =>
      simp [intervalSearch?]
  | node left int _ right ihLeft ihRight =>
      intro h
      rcases hB with ⟨hBL, hBR, _hLeftLE, _hRightGE⟩
      rcases hW with ⟨hWL, hWR, _hMax⟩
      unfold intervalSearch? at h
      by_cases hO : Interval.overlaps int q = true
      · -- current interval overlaps
        simp [hO] at h
        cases h with
        | refl =>
            constructor
            · simp [keys_node]
            · simp [hO]
      · -- current interval does not overlap
        by_cases hL : goLeft left q = true
        · -- go left
          simp [hO, hL] at h
          have hIh := ihLeft hBL hWL h
          constructor
          · simp [keys_node, hIh.1]
          · exact hIh.2
        · -- go right
          simp [hO, hL] at h
          have hIh := ihRight hBR hWR h
          constructor
          · simp [keys_node, hIh.1]
          · exact hIh.2

/-- If the executable interval search returns none, no interval in the tree
overlaps the query. -/
theorem intervalSearch?_none_noOverlap {t : IntervalTree} (hB : IsBST t) (hW : WellAugmented t)
    (q : Interval) :
    intervalSearch? t q = none → ¬ hasOverlap t q := by
  induction t with
  | empty =>
      simp [intervalSearch?, hasOverlap]
  | node left int mx right ihLeft ihRight =>
      intro h
      rcases hB with ⟨hBL, hBR, hLeftLE, hRightGE⟩
      rcases hW with ⟨hWL, hWR, _hMax⟩
      unfold intervalSearch? at h
      by_cases hO : Interval.overlaps int q = true
      · -- current overlaps, but returned none: impossible
        simp [hO] at h
      · -- current interval does not overlap
        by_cases hL : goLeft left q = true
        · -- went left and got none
          simp [hO, hL] at h
          have hNoLeft : ¬ hasOverlap left q := ihLeft hBL hWL h
          intro hOv
          rcases hOv with ⟨j, hj, hov⟩
          simp [keys_node] at hj
          rcases hj with (hjLeft | hjEq | hjRight)
          · -- overlap in left subtree
            exact hNoLeft ⟨j, hjLeft, hov⟩
          · -- overlap with current interval
            rw [hjEq] at hov
            exact hO hov
          · -- overlap in right subtree forces one in left subtree
            have hRightEx : ∃ j ∈ keys right, Interval.overlaps j q := ⟨j, hjRight, hov⟩
            have hL' := goLeft_true hL
            have hLeftOverlap := overlap_left_of_right_overlap mx ⟨hBL, hBR, hLeftLE, hRightGE⟩
              (by rw [← storedMaxHigh_eq_realMaxHigh_of_wellAugmented hWL]; exact hL'.2)
              hO hRightEx
            rcases hLeftOverlap with ⟨k, hk, hkov⟩
            exact hNoLeft ⟨k, hk, hkov⟩
        · -- went right and got none
          have hL_false : goLeft left q = false := by simp [hL]
          simp [hO, hL] at h
          have hNoRight : ¬ hasOverlap right q := ihRight hBR hWR h
          intro hOv
          rcases hOv with ⟨j, hj, hov⟩
          simp [keys_node] at hj
          rcases hj with (hjLeft | hjEq | hjRight)
          · -- no overlap possible in left subtree
            have hNoLeft : ¬ hasOverlap left q := by
              rcases goLeft_false hL_false with hEmpty | hmax
              · simp [hEmpty, hasOverlap]
              · have hmax' : realMaxHigh left < q.low := by
                  rw [← storedMaxHigh_eq_realMaxHigh_of_wellAugmented hWL]
                  exact hmax
                intro hOv'
                exact noOverlap_of_realMaxHigh_lt hmax' hOv'
            exact hNoLeft ⟨j, hjLeft, hov⟩
          · -- overlap with current interval
            rw [hjEq] at hov
            exact hO hov
          · -- overlap in right subtree
            exact hNoRight ⟨j, hjRight, hov⟩

/-- Combined correctness specification for interval search. -/
theorem intervalSearch?_spec {t : IntervalTree} (hB : IsBST t) (hW : WellAugmented t)
    (q : Interval) :
    (intervalSearch? t q = none ↔ ¬ hasOverlap t q) ∧
    (∀ i, intervalSearch? t q = some i → i ∈ keys t ∧ Interval.overlaps i q) := by
  constructor
  · constructor
    · exact intervalSearch?_none_noOverlap hB hW q
    · intro hNoOverlap
      by_contra h
      have : intervalSearch? t q ≠ none := by
        simp [h]
      rcases Option.ne_none_iff_exists'.mp this with ⟨i, hi⟩
      have := intervalSearch?_some_overlap hB hW q i hi
      exact hNoOverlap ⟨i, this.1, this.2⟩
  · exact intervalSearch?_some_overlap hB hW q

end IntervalTree

/-! ## Red-black bridge: maintaining an augmentation through Chapter 13 rotations

CLRS Theorem 14.1 in the red-black setting: a locally-computable augmentation
can be maintained through the structural primitives used by red-black insertion
and deletion.  Chapter 13's red-black rotations and root recoloring are exactly
those primitives.  We show that any rotation-invariant augmentation's *value*
is preserved by these operations — so a locally-recomputed cached field stays
correct — reusing the same {lit}`IsRotationInvariant` law as the generic framework.

Note: red-black rotations are shape-*restoring*, not shape-*preserving*: they are
applied mid-fixup where {lit}`RedBlackShape` is temporarily broken, so we do not
(and cannot) claim a single rotation preserves {lit}`RedBlackShape`.
{lit}`RedBlackShape` maintenance across a full insertion is Chapter 13's
{lit}`RBTree.redBlackShape_insert`; the new content here is that the augmentation
rides along invariantly under the same rotations and recoloring. -/

namespace RBBridge

open CLRS.Chapter13

/-- Inorder key list of a Chapter 13 red-black tree. -/
def rbKeys : RBTree → List Nat
  | .empty => []
  | .node _ l k r => rbKeys l ++ [k] ++ rbKeys r

/-- Semantic value of an augmentation on a red-black tree, computed from each
key and its children (independent of node colors). -/
def rbRealAug {β : Type} [Inhabited β] (aug : Augmentation Nat β) : RBTree → β
  | .empty => aug.base
  | .node _ l k r => aug.combine k (rbRealAug aug l) (rbRealAug aug r)

/-- Left rotation preserves the inorder key list. -/
theorem rbKeys_rotateLeft (t : RBTree) :
    rbKeys (RBTree.rotateLeft t) = rbKeys t := by
  cases t with
  | empty => rfl
  | node color a x right =>
      cases right with
      | empty => rfl
      | node rc b y c => simp [RBTree.rotateLeft, rbKeys, List.append_assoc]

/-- Right rotation preserves the inorder key list. -/
theorem rbKeys_rotateRight (t : RBTree) :
    rbKeys (RBTree.rotateRight t) = rbKeys t := by
  cases t with
  | empty => rfl
  | node color left y c =>
      cases left with
      | empty => rfl
      | node lc a x b => simp [RBTree.rotateRight, rbKeys, List.append_assoc]

/-- Left rotation preserves any rotation-invariant augmentation's value. -/
theorem rbRealAug_rotateLeft {β : Type} [Inhabited β] (aug : Augmentation Nat β)
    [IsRotationInvariant aug] (t : RBTree) :
    rbRealAug aug (RBTree.rotateLeft t) = rbRealAug aug t := by
  cases t with
  | empty => rfl
  | node color a x right =>
      cases right with
      | empty => rfl
      | node rc b y c =>
          simp only [RBTree.rotateLeft, rbRealAug]
          rw [IsRotationInvariant.combine_rotate]

/-- Right rotation preserves any rotation-invariant augmentation's value. -/
theorem rbRealAug_rotateRight {β : Type} [Inhabited β] (aug : Augmentation Nat β)
    [IsRotationInvariant aug] (t : RBTree) :
    rbRealAug aug (RBTree.rotateRight t) = rbRealAug aug t := by
  cases t with
  | empty => rfl
  | node color left y c =>
      cases left with
      | empty => rfl
      | node lc a x b =>
          simp only [RBTree.rotateRight, rbRealAug]
          rw [IsRotationInvariant.combine_rotate]

/-- Root recoloring preserves the augmentation value. -/
theorem rbRealAug_repaintRoot {β : Type} [Inhabited β] (aug : Augmentation Nat β)
    (c : Color) (t : RBTree) :
    rbRealAug aug (RBTree.repaintRoot c t) = rbRealAug aug t := by
  cases t <;> simp [RBTree.repaintRoot, rbRealAug]

/-- **Red-black bridge (CLRS Theorem 14.1, red-black primitives).**  Every
structural primitive used by red-black insertion and deletion — left and right
rotation and root recoloring — preserves both the inorder key sequence and any
rotation-invariant augmentation's value.  Hence the augmentation can be
maintained through the red-black operations by local recomputation, exactly as
in the generic framework. -/
theorem rb_augmentation_bridge {β : Type} [Inhabited β] (aug : Augmentation Nat β)
    [IsRotationInvariant aug] :
    (∀ t, rbKeys (RBTree.rotateLeft t) = rbKeys t) ∧
    (∀ t, rbKeys (RBTree.rotateRight t) = rbKeys t) ∧
    (∀ t, rbRealAug aug (RBTree.rotateLeft t) = rbRealAug aug t) ∧
    (∀ t, rbRealAug aug (RBTree.rotateRight t) = rbRealAug aug t) ∧
    (∀ (c : Color) (t), rbRealAug aug (RBTree.repaintRoot c t) = rbRealAug aug t) :=
  ⟨rbKeys_rotateLeft, rbKeys_rotateRight,
   rbRealAug_rotateLeft aug, rbRealAug_rotateRight aug,
   fun c t => rbRealAug_repaintRoot aug c t⟩

/-- The size augmentation's value on a red-black tree is its node count. -/
theorem rbRealAug_sizeAug_eq_length (t : RBTree) :
    rbRealAug (sizeAug Nat) t = (rbKeys t).length := by
  induction t with
  | empty => rfl
  | node c l k r ihl ihr =>
      simp only [rbRealAug, rbKeys]
      rw [ihl, ihr]
      simp only [sizeAug, List.length_append, List.length_cons, List.length_nil]
      omega

end RBBridge

/-! ## General augmentation interface: an arbitrary augmentation through
executable red-black insertion

This section closes the "stored-field refinement" gap noted above, at the
*generic* level.  Section 14.1's {lit}`OSRBTree` threaded only the concrete
subtree-*size* augmentation through Chapter 13's executable red-black insertion,
in a bespoke, size-specific type.  Here we thread an **arbitrary**
{name}`Augmentation` through the same Okasaki-style balancer, so both the
order-statistic (size) and interval (max-high) augmentations are recovered as
instances of a single generic interface.

The augmented red-black tree {lit}`AugmentedRBTree` caches, at every internal
node, a node colour (reusing Chapter 13's {name}`CLRS.Chapter13.Color`) and an
augmentation value of type {lit}`β`.  Every reconstructed node is built by the
smart constructor {lit}`AugmentedRBTree.mk`, which recomputes the cached
augmentation from its children via {lit}`aug.combine`.  Two bridges connect this
to the existing development:

* {lit}`AugmentedRBTree.wellAugmented_insert`: **the augmentation invariant
  survives balancing** — inserting into a well-augmented tree yields a
  well-augmented tree, for any augmentation (CLRS 14.1 maintained through
  {lit}`RB-INSERT`).
* {lit}`AugmentedRBTree.toRB_insert`: erasing the augmentation field commutes
  with insertion, so (for {lit}`Nat` keys) the augmented insert refines the
  *executable* Chapter 13 {name}`CLRS.Chapter13.RBTree.insert` exactly,
  transferring its shape and membership theorems.

The size and max-high fields are then recovered as instances via
{lit}`AugmentedRBTree.sizeAug_wellAugmented_insert` and
{lit}`AugmentedRBTree.maxHighAug_wellAugmented_insert`.
-/

open CLRS.Chapter13 (Color RBTree)

/--
A red-black tree augmented with a cached value of type {lit}`β` at every internal
node.  Each node stores a colour (reusing Chapter 13's
{name}`CLRS.Chapter13.Color`), a key of type {lit}`α`, a cached augmentation of
type {lit}`β`, and two subtrees.  This is the colour-carrying refinement of
{name}`AugmentedTree`, adding the field needed to run the Chapter 13 insertion
balancer generically.
-/
inductive AugmentedRBTree (α β : Type) where
  | empty : AugmentedRBTree α β
  | node : Color → AugmentedRBTree α β → α → β → AugmentedRBTree α β → AugmentedRBTree α β
  deriving Repr, DecidableEq

namespace AugmentedRBTree

section Generic

variable {α β : Type} [Inhabited β] (aug : Augmentation α β)

/-- Inorder traversal of the keys, ignoring colours and cached augmentations. -/
def keys : AugmentedRBTree α β → List α
  | empty => []
  | node _ l k _ r => keys l ++ [k] ++ keys r

/-- The cached augmentation stored at the root; the empty tree uses {lit}`aug.base`. -/
def storedAug : AugmentedRBTree α β → β
  | empty => aug.base
  | node _ _ _ a _ => a

/-- The mathematically correct augmentation, recomputed from the children. -/
def realAug : AugmentedRBTree α β → β
  | empty => aug.base
  | node _ l k _ r => aug.combine k (realAug l) (realAug r)

/-- Every cached augmentation agrees with the recomputed one. -/
def WellAugmented : AugmentedRBTree α β → Prop
  | empty => True
  | node _ l k a r =>
      WellAugmented l ∧ WellAugmented r ∧
        a = aug.combine k (realAug aug l) (realAug aug r)

/--
Smart constructor that recomputes the cached augmentation from the children.
Every node produced by the red-black operations below is built with {name}`mk`,
which is why the {name}`WellAugmented` invariant is preserved automatically.
-/
def mk (c : Color) (l : AugmentedRBTree α β) (k : α) (r : AugmentedRBTree α β) :
    AugmentedRBTree α β :=
  node c l k (aug.combine k (realAug aug l) (realAug aug r)) r

/-- {name}`mk` recomputes the augmentation correctly. -/
theorem realAug_mk (c : Color) (l : AugmentedRBTree α β) (k : α) (r : AugmentedRBTree α β) :
    realAug aug (mk aug c l k r) = aug.combine k (realAug aug l) (realAug aug r) := rfl

/-- {name}`mk` preserves the inorder key sequence. -/
theorem keys_mk (c : Color) (l : AugmentedRBTree α β) (k : α) (r : AugmentedRBTree α β) :
    keys (mk aug c l k r) = keys l ++ [k] ++ keys r := rfl

/-- The cached root augmentation of a {name}`mk` node is the recomputed value. -/
theorem storedAug_mk (c : Color) (l : AugmentedRBTree α β) (k : α) (r : AugmentedRBTree α β) :
    storedAug aug (mk aug c l k r) = aug.combine k (realAug aug l) (realAug aug r) := rfl

/-- A {name}`mk` node is well-augmented whenever both children are. -/
theorem wellAugmented_mk {c : Color} {l : AugmentedRBTree α β} {k : α} {r : AugmentedRBTree α β}
    (hl : WellAugmented aug l) (hr : WellAugmented aug r) :
    WellAugmented aug (mk aug c l k r) :=
  ⟨hl, hr, rfl⟩

/-- A well-augmented tree has a correct root augmentation. -/
theorem storedAug_eq_realAug_of_wellAugmented {t : AugmentedRBTree α β}
    (h : WellAugmented aug t) : storedAug aug t = realAug aug t := by
  cases t with
  | empty => rfl
  | node c l k a r => exact h.2.2

/-! ### Executable red-black operations with augmentation recomputation -/

/-- Repaint the root black, keeping the cached augmentation fields. -/
def repaintBlack : AugmentedRBTree α β → AugmentedRBTree α β
  | empty => empty
  | node _ l k a r => node Color.black l k a r

/--
Okasaki-style rebalance after insertion on the left child, recomputing
augmentations.  Mirrors {name}`CLRS.Chapter13.RBTree.balanceLeft`.
-/
def balanceLeft (l : AugmentedRBTree α β) (y : α) (r : AugmentedRBTree α β) :
    AugmentedRBTree α β :=
  match l with
  | node Color.red (node Color.red a w _ b) x _ c =>
      mk aug Color.red (mk aug Color.black a w b) x (mk aug Color.black c y r)
  | node Color.red a w _ (node Color.red b x _ c) =>
      mk aug Color.red (mk aug Color.black a w b) x (mk aug Color.black c y r)
  | _ => mk aug Color.black l y r

/--
Okasaki-style rebalance after insertion on the right child, recomputing
augmentations.  Mirrors {name}`CLRS.Chapter13.RBTree.balanceRight`.
-/
def balanceRight (l : AugmentedRBTree α β) (y : α) (r : AugmentedRBTree α β) :
    AugmentedRBTree α β :=
  match r with
  | node Color.red (node Color.red b x _ c) y' _ d =>
      mk aug Color.red (mk aug Color.black l y b) x (mk aug Color.black c y' d)
  | node Color.red b x _ (node Color.red c y' _ d) =>
      mk aug Color.red (mk aug Color.black l y b) x (mk aug Color.black c y' d)
  | _ => mk aug Color.black l y r

/--
Insertion fixup: recurse down by the Boolean comparison {lit}`lt`, rebuilding and
rebalancing with augmentation recomputation on the way back up.  Mirrors
{name}`CLRS.Chapter13.RBTree.insertFixup`.
-/
def insertFixup (lt : α → α → Bool) (x : α) : AugmentedRBTree α β → AugmentedRBTree α β
  | empty => mk aug Color.red empty x empty
  | node c l y a r =>
      if lt x y then
        if c = Color.black then balanceLeft aug (insertFixup lt x l) y r
        else mk aug Color.red (insertFixup lt x l) y r
      else if lt y x then
        if c = Color.black then balanceRight aug l y (insertFixup lt x r)
        else mk aug Color.red l y (insertFixup lt x r)
      else node c l y a r

/-- Insert a key and repaint the root black. -/
def insert (lt : α → α → Bool) (x : α) (t : AugmentedRBTree α β) : AugmentedRBTree α β :=
  repaintBlack (insertFixup aug lt x t)

/-! ### The augmentation invariant survives balancing (CLRS 14.1 through RB-INSERT) -/

/-- Repainting the root black preserves the {name}`WellAugmented` invariant. -/
theorem wellAugmented_repaintBlack {t : AugmentedRBTree α β} (h : WellAugmented aug t) :
    WellAugmented aug (repaintBlack t) := by
  cases t with
  | empty => trivial
  | node c l k a r => exact ⟨h.1, h.2.1, h.2.2⟩

/-- {name}`balanceLeft` preserves the {name}`WellAugmented` invariant. -/
theorem wellAugmented_balanceLeft {l : AugmentedRBTree α β} {y : α} {r : AugmentedRBTree α β}
    (hl : WellAugmented aug l) (hr : WellAugmented aug r) :
    WellAugmented aug (balanceLeft aug l y r) := by
  unfold balanceLeft
  split
  · obtain ⟨⟨ha, hb, _⟩, hc, _⟩ := hl
    exact wellAugmented_mk aug (wellAugmented_mk aug ha hb) (wellAugmented_mk aug hc hr)
  · obtain ⟨ha, ⟨hb, hc, _⟩, _⟩ := hl
    exact wellAugmented_mk aug (wellAugmented_mk aug ha hb) (wellAugmented_mk aug hc hr)
  · exact wellAugmented_mk aug hl hr

/-- {name}`balanceRight` preserves the {name}`WellAugmented` invariant. -/
theorem wellAugmented_balanceRight {l : AugmentedRBTree α β} {y : α} {r : AugmentedRBTree α β}
    (hl : WellAugmented aug l) (hr : WellAugmented aug r) :
    WellAugmented aug (balanceRight aug l y r) := by
  unfold balanceRight
  split
  · obtain ⟨⟨hb, hc, _⟩, hd, _⟩ := hr
    exact wellAugmented_mk aug (wellAugmented_mk aug hl hb) (wellAugmented_mk aug hc hd)
  · obtain ⟨hb, ⟨hc, hd, _⟩, _⟩ := hr
    exact wellAugmented_mk aug (wellAugmented_mk aug hl hb) (wellAugmented_mk aug hc hd)
  · exact wellAugmented_mk aug hl hr

/-- {name}`insertFixup` preserves the {name}`WellAugmented` invariant. -/
theorem wellAugmented_insertFixup (lt : α → α → Bool) (x : α) {t : AugmentedRBTree α β}
    (h : WellAugmented aug t) : WellAugmented aug (insertFixup aug lt x t) := by
  induction t with
  | empty =>
      simp only [insertFixup]
      exact wellAugmented_mk aug (by trivial) (by trivial)
  | node c l y a r ihl ihr =>
      have hl : WellAugmented aug l := h.1
      have hr : WellAugmented aug r := h.2.1
      simp only [insertFixup]
      split
      · split
        · exact wellAugmented_balanceLeft aug (ihl hl) hr
        · exact wellAugmented_mk aug (ihl hl) hr
      · split
        · split
          · exact wellAugmented_balanceRight aug hl (ihr hr)
          · exact wellAugmented_mk aug hl (ihr hr)
        · exact h

/--
**Augmentation invariant through executable insertion (CLRS 14.1 through
`RB-INSERT`).**  Inserting a key into a well-augmented augmented red-black tree
produces a well-augmented tree: every cached augmentation field remains correct
after the red-black rebalancing, for *any* {name}`Augmentation`.  This
generalizes {lit}`OSRBTree.wellSized_insert` from the size field to an
arbitrary augmentation.
-/
theorem wellAugmented_insert (lt : α → α → Bool) (x : α) {t : AugmentedRBTree α β}
    (h : WellAugmented aug t) : WellAugmented aug (insert aug lt x t) := by
  unfold insert
  exact wellAugmented_repaintBlack aug (wellAugmented_insertFixup aug lt x h)

/-- After insertion the cached root augmentation equals the recomputed value. -/
theorem storedAug_insert (lt : α → α → Bool) (x : α) {t : AugmentedRBTree α β}
    (h : WellAugmented aug t) :
    storedAug aug (insert aug lt x t) = realAug aug (insert aug lt x t) :=
  storedAug_eq_realAug_of_wellAugmented aug (wellAugmented_insert aug lt x h)

end Generic

section Refinement

variable {β : Type} [Inhabited β] (aug : Augmentation Nat β)

/-- Erase the cached augmentation field, projecting a {lit}`Nat`-keyed augmented
red-black tree onto the Chapter 13 red-black tree. -/
def toRB : AugmentedRBTree Nat β → RBTree
  | empty => RBTree.empty
  | node c l k _ r => RBTree.node c (toRB l) k (toRB r)

/-- The {lit}`Nat` strict-less-than comparison as a {lit}`Bool`, used to
instantiate the generic insertion so that it refines Chapter 13's
{name}`CLRS.Chapter13.RBTree.insert`. -/
def natLt (a b : Nat) : Bool := decide (a < b)

/-- {name}`natLt` decides strict less-than. -/
theorem natLt_true_iff {a b : Nat} : (natLt a b = true) ↔ a < b := by
  simp [natLt]

/-- Erasing the augmentation of a {name}`mk` node forgets only the cached value. -/
theorem toRB_mk (c : Color) (l : AugmentedRBTree Nat β) (k : Nat) (r : AugmentedRBTree Nat β) :
    toRB (mk aug c l k r) = RBTree.node c (toRB l) k (toRB r) := rfl

omit [Inhabited β] in
/-- Erasing the augmentation commutes with repainting the root black. -/
theorem toRB_repaintBlack (t : AugmentedRBTree Nat β) :
    toRB (repaintBlack t) = RBTree.repaintRoot Color.black (toRB t) := by
  cases t with
  | empty => rfl
  | node c l k a r => rfl

/-- Erasing the augmentation commutes with {name}`balanceLeft`. -/
theorem toRB_balanceLeft (l : AugmentedRBTree Nat β) (y : Nat) (r : AugmentedRBTree Nat β) :
    toRB (balanceLeft aug l y r) = RBTree.balanceLeft (toRB l) y (toRB r) := by
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

/-- Erasing the augmentation commutes with {name}`balanceRight`. -/
theorem toRB_balanceRight (l : AugmentedRBTree Nat β) (y : Nat) (r : AugmentedRBTree Nat β) :
    toRB (balanceRight aug l y r) = RBTree.balanceRight (toRB l) y (toRB r) := by
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

/-- Erasing the augmentation commutes with {name}`insertFixup` (at {name}`natLt`). -/
theorem toRB_insertFixup (x : Nat) (t : AugmentedRBTree Nat β) :
    toRB (insertFixup aug natLt x t) = RBTree.insertFixup x (toRB t) := by
  induction t with
  | empty => rfl
  | node c l y a r ihl ihr =>
      simp only [insertFixup, RBTree.insertFixup, toRB, natLt_true_iff, gt_iff_lt,
        apply_ite toRB, toRB_mk, toRB_balanceLeft, toRB_balanceRight, ihl, ihr]

/--
**Refinement.**  The augmented insertion refines the *executable* Chapter 13
red-black insertion: erasing the cached augmentation turns {name}`insert` (at
{name}`natLt`) into {name}`CLRS.Chapter13.RBTree.insert`.  This generalizes
{lit}`OSRBTree.toRB_insert` from the size field to an arbitrary augmentation.
-/
theorem toRB_insert (x : Nat) (t : AugmentedRBTree Nat β) :
    toRB (insert aug natLt x t) = RBTree.insert x (toRB t) := by
  unfold insert RBTree.insert
  rw [toRB_repaintBlack, toRB_insertFixup]

omit [Inhabited β] in
/-- Erasure relates {name}`keys` membership to Chapter 13 tree membership. -/
theorem inTree_toRB (y : Nat) (t : AugmentedRBTree Nat β) :
    RBTree.InTree y (toRB t) ↔ y ∈ keys t := by
  induction t with
  | empty => simp [toRB, RBTree.InTree, keys]
  | node c l k a r ihl ihr =>
      simp only [toRB, RBTree.InTree, keys, List.append_assoc, List.singleton_append,
        List.mem_append, List.mem_cons, ihl, ihr]
      tauto

/--
Through the refinement, the Chapter 13 red-black shape invariant is maintained by
the augmented insertion.
-/
theorem redBlackShape_toRB_insert (x : Nat) {t : AugmentedRBTree Nat β}
    (h : RBTree.RedBlackShape (toRB t)) :
    RBTree.RedBlackShape (toRB (insert aug natLt x t)) := by
  rw [toRB_insert]
  exact RBTree.redBlackShape_insert h

/-- Through the refinement, insertion preserves membership (as an inorder key). -/
theorem mem_keys_insert (x y : Nat) (t : AugmentedRBTree Nat β) :
    y ∈ keys (insert aug natLt x t) ↔ y = x ∨ y ∈ keys t := by
  simp only [← inTree_toRB, toRB_insert, RBTree.inTree_insert_iff]

end Refinement

section Instances

/-! ### Instance 1: the order-statistic (subtree-size) augmentation

Taking {lit}`aug := sizeAug Nat` recovers the order-statistic tree of §14.1: the
cached field is the subtree node count, the invariant survives the executable
red-black insertion, and the augmentation-erasing projection refines Chapter 13's
{name}`CLRS.Chapter13.RBTree.insert`.  This makes {lit}`OSRBTree` a special case
of the generic interface rather than a bespoke copy. -/

/-- **Order-statistic instance.**  The subtree-size augmentation is maintained
through the generic executable red-black insertion (CLRS 14.1 for size). -/
theorem sizeAug_wellAugmented_insert (x : Nat) {t : AugmentedRBTree Nat Nat}
    (h : WellAugmented (sizeAug Nat) t) :
    WellAugmented (sizeAug Nat) (insert (sizeAug Nat) natLt x t) :=
  wellAugmented_insert (sizeAug Nat) natLt x h

/-- The size augmentation's recomputed value is exactly the node count. -/
theorem sizeAug_realAug_eq_length (t : AugmentedRBTree Nat Nat) :
    realAug (sizeAug Nat) t = (keys t).length := by
  induction t with
  | empty => rfl
  | node c l k a r ihl ihr =>
      simp only [realAug]
      rw [ihl, ihr]
      simp only [sizeAug, keys, List.length_append, List.length_cons, List.length_nil]
      omega

/-- **Order-statistic refinement.**  Erasing the size field turns the generic
size-augmented insertion into Chapter 13's {name}`CLRS.Chapter13.RBTree.insert`. -/
theorem sizeAug_toRB_insert (x : Nat) (t : AugmentedRBTree Nat Nat) :
    toRB (insert (sizeAug Nat) natLt x t) = RBTree.insert x (toRB t) :=
  toRB_insert (sizeAug Nat) x t

/-! ### Instance 2: the interval-tree (maximum-high-endpoint) augmentation

Taking {lit}`aug := IntervalTree.maxHighAug` recovers interval trees: the cached
field is the subtree's maximum high endpoint, maintained through the same generic
executable insertion, with the BST order taken on interval low endpoints. -/

/-- BST comparison for interval trees: order by the interval's low endpoint. -/
def intervalLt (i j : Interval) : Bool := natLt i.low j.low

/-- **Interval-tree instance.**  The maximum-high-endpoint augmentation is
maintained through the generic executable red-black insertion. -/
theorem maxHighAug_wellAugmented_insert (q : Interval) {t : AugmentedRBTree Interval Nat}
    (h : WellAugmented IntervalTree.maxHighAug t) :
    WellAugmented IntervalTree.maxHighAug (insert IntervalTree.maxHighAug intervalLt q t) :=
  wellAugmented_insert IntervalTree.maxHighAug intervalLt q h

end Instances

end AugmentedRBTree
