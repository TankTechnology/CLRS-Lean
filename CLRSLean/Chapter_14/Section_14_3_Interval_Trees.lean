import Mathlib
import CLRSLean.Chapter_13.Section_13_1_Red_Black_Trees

/-! # Section 14.3 - Interval trees

This file formalizes the second classic augmentation from CLRS Chapter 14:
interval trees.  Each node stores an interval and a cached maximum high endpoint
of its subtree.  The search algorithm uses the cached maximum to prune the left
subtree when no overlap is possible there.

To make the pattern reusable, we first define a small generic augmentation
framework: an `AugmentedTree α β` carries a value of type `α` at each node and
a cached augmentation of type `β`.  An `Augmentation α β` provides the empty
default and the local recombination function.  The framework proves that
recomputing the augmentation from the children preserves the `WellAugmented`
invariant, and that rotations preserve the inorder key sequence and the
`WellAugmented` invariant for augmentations whose combine operator behaves like
`max` (which is the case for the interval-tree instantiation).  We then
instantiate it to interval trees with the max-high augmentation, and show that
the executable `intervalSearch?` is correct on well-augmented BSTs.

Main results:

* Generic `AugmentedTree` lemmas: `keys_recompute`, `realAug_recompute`,
  `recompute_wellAugmented`, `rotateLeft_wellAugmented`,
  `rotateRight_wellAugmented`.
* Interval-tree correctness: `intervalSearch?_some_overlap` and
  `intervalSearch?_none_noOverlap` (combined as `intervalSearch?_spec`).

Current gaps:

* A red-black bridge (`ofRBTree`) and a full `RB-INSERT` / `RB-DELETE` that
  maintain both color and max-high augmentation remain future work.
* The generic framework uses a fixed augmentation type per tree; a fully
  monoid-based augmentation theorem is not attempted.
-/

namespace CLRS
namespace Chapter14

/-! ## Generic augmented trees -/

/-- An augmentation schema for a binary tree: a default for the empty tree and
a local recombination function. -/
structure Augmentation (α β : Type) [Inhabited β] where
  base : β
  combine : α → β → β → β

/-- Typeclass asserting that an augmentation's `combine` operation satisfies the
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

end AugmentedTree

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

/-- Every interval in the tree has low endpoint at most `x`. -/
def allLowLE (t : IntervalTree) (x : Nat) : Prop :=
  ∀ i ∈ keys t, i.low ≤ x

/-- Every interval in the tree has low endpoint at least `x`. -/
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

/-- A true `goLeft` condition means the left subtree is non-empty and its max-high
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

/-- A false `goLeft` condition means the left subtree is empty or its max-high is
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

/-- Membership in `keys` respects the inorder list membership relation. -/
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

/-- `hasOverlap` distributes over a node in the obvious way. -/
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
