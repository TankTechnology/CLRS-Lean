import Mathlib
import CLRSLean.Chapter_14.Section_14_3_Interval_Trees

/-!
# Section 17.3 - Interval trees

This section closes the fourth-edition §17.3 boundary.  The legacy
{lit}`CLRSLean.Chapter_14` development proves the static interval-search model —
{lit}`IntervalTree.intervalSearch?_spec` — and threads the max-high augmentation
through executable red-black insertion
({lit}`AugmentedRBTree.maxHighAug_wellAugmented_insert`).  What remains is the
**bridge** connecting the dynamic augmented red-black representation to the
static search spec, together with the search's logarithmic-cost foundation.

Main results:

- Definition {lit}`IntervalTree.intervalSearchCost`: the pointer cost of
  {lit}`IntervalSearch`.
- Theorem {lit}`IntervalTree.intervalSearchCost_le_height`: the search cost is
  bounded by the tree height (the logarithmic-cost foundation).
- Definition {lit}`AugmentedRBTree.toIntervalTree`: erasure of the dynamic
  augmented red-black tree to the static interval tree.
- Theorem {lit}`AugmentedRBTree.wellAugmented_toIntervalTree`: erasure preserves
  the max-high augmentation, bridging the dynamic and static representations.
- Theorem {lit}`intervalSearch_after_update`: **search-after-update** — the
  erasure of a max-high-augmented dynamic tree is well-augmented, so the static
  search specification {lit}`IntervalTree.intervalSearch?_spec` remains
  applicable after an update.
- Definition {lit}`AugmentedRBTree.toRB_low`: erasure of the dynamic
  {lit}`Interval`-keyed augmented red-black tree to the Chapter 13 red-black
  tree, projecting each interval key to its low endpoint.
- Theorem {lit}`intervalSearchCost_log_bound`: **interval search runs in
  {lit}`O(log n)`** — composing {lit}`intervalSearchCost_le_height` with the
  red-black height bound ({lit}`RBTree.height_log_bound`) through the
  height-erasure equality {lit}`AugmentedRBTree.intervalHeight_eq_toRB_height`.
-/

namespace CLRS
namespace Chapter14

namespace IntervalTree

/-- The height of an interval tree (maximum depth of the augmented tree). -/
def intervalHeight : IntervalTree → Nat
  | AugmentedTree.empty => 0
  | AugmentedTree.node l _ _ r => 1 + max (intervalHeight l) (intervalHeight r)

/-- The pointer-operation cost of {lit}`intervalSearch?`: one node visit per
level of the root-to-leaf descent. -/
def intervalSearchCost : IntervalTree → Interval → Nat
  | AugmentedTree.empty, _ => 0
  | AugmentedTree.node l _ _ r, q =>
      1 + if goLeft l q then intervalSearchCost l q else intervalSearchCost r q

/-- The interval-search cost is bounded by the tree height plus one. -/
theorem intervalSearchCost_le_height (t : IntervalTree) (q : Interval) :
    intervalSearchCost t q ≤ intervalHeight t + 1 := by
  induction t generalizing q with
  | empty => simp [intervalSearchCost, intervalHeight]
  | node l int a r ihl ihr =>
    simp only [intervalSearchCost, intervalHeight]
    by_cases h : goLeft l q
    · simp [h]
      have ih := ihl q
      have hmax : intervalHeight l ≤ max (intervalHeight l) (intervalHeight r) := Nat.le_max_left _ _
      omega
    · simp [h]
      have ih := ihr q
      have hmax : intervalHeight r ≤ max (intervalHeight l) (intervalHeight r) := Nat.le_max_right _ _
      omega

end IntervalTree

namespace AugmentedRBTree

/-- Erase the colors of a dynamic augmented red-black interval tree, projecting
it onto the static {lit}`IntervalTree`. -/
def toIntervalTree : AugmentedRBTree Interval Nat → IntervalTree
  | empty => AugmentedTree.empty
  | node _ l k a r => AugmentedTree.node (toIntervalTree l) k a (toIntervalTree r)

/-- Erasing colors preserves the mathematical max-high augmentation. -/
theorem realAug_toIntervalTree (t : AugmentedRBTree Interval Nat) :
    AugmentedTree.realAug IntervalTree.maxHighAug (toIntervalTree t) =
      realAug IntervalTree.maxHighAug t := by
  induction t with
  | empty => rfl
  | node c l k a r ihl ihr =>
    simp [toIntervalTree, AugmentedTree.realAug, realAug, ihl, ihr]

/-- The erasure of a well-augmented dynamic interval tree is a well-augmented
static interval tree (with the max-high augmentation). -/
theorem wellAugmented_toIntervalTree {t : AugmentedRBTree Interval Nat}
    (h : WellAugmented IntervalTree.maxHighAug t) :
    IntervalTree.WellAugmented (toIntervalTree t) := by
  induction t with
  | empty => simp [toIntervalTree, IntervalTree.WellAugmented]
  | node c l k a r ihl ihr =>
    obtain ⟨hL, hR, ha⟩ := h
    change AugmentedTree.WellAugmented IntervalTree.maxHighAug
      (AugmentedTree.node (toIntervalTree l) k a (toIntervalTree r))
    constructor
    · exact ihl hL
    constructor
    · exact ihr hR
    · simp only [AugmentedTree.realAug]
      rw [realAug_toIntervalTree l, realAug_toIntervalTree r]
      exact ha

end AugmentedRBTree

/-! ## The dynamic/static bridge and search-after-update -/

/-- **Search-after-update.**  Inserting an interval into a well-augmented dynamic
interval tree yields a tree whose erasure is still well-augmented, so the static
search specification {lit}`IntervalTree.intervalSearch?_spec` remains applicable
after the update. -/
theorem intervalSearch_after_update (q : Interval) {t : AugmentedRBTree Interval Nat}
    (h : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug t) :
    IntervalTree.WellAugmented
      (AugmentedRBTree.toIntervalTree
        (AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt q t)) := by
  exact AugmentedRBTree.wellAugmented_toIntervalTree
    (AugmentedRBTree.maxHighAug_wellAugmented_insert q h)

/-! ## The Interval-keyed O(log n) search bound -/

open CLRS.Chapter13 (RBTree)

namespace AugmentedRBTree

/-- Erase the interval keys (keeping their low endpoint) and the cached
augmentation, projecting an {lit}`Interval`-keyed augmented red-black tree onto
the Chapter 13 {lit}`RBTree`. -/
def toRB_low : AugmentedRBTree Interval Nat → RBTree
  | empty => RBTree.empty
  | node c l k _ r => RBTree.node c (toRB_low l) k.low (toRB_low r)

/-- The height of the static interval erasure equals the height of the low-keyed
red-black erasure: heights depend on neither keys, colors, nor the cached
augmentation. -/
theorem intervalHeight_eq_toRB_height (t : AugmentedRBTree Interval Nat) :
    IntervalTree.intervalHeight (toIntervalTree t) = RBTree.height (toRB_low t) := by
  induction t with
  | empty => rfl
  | node c l k a r ihl ihr =>
    simp [toIntervalTree, toRB_low, IntervalTree.intervalHeight, RBTree.height, ihl, ihr]

end AugmentedRBTree

/-- **Interval search runs in {lit}`O(log n)`.**  On an {lit}`Interval`-keyed
augmented red-black tree with {lit}`n` nodes, interval search performs at most
{lit}`2 log₂(n+1) + 1` pointer operations, composing
{lit}`intervalSearchCost_le_height` with the red-black height bound
({lit}`RBTree.height_log_bound`) via {lit}`AugmentedRBTree.intervalHeight_eq_toRB_height`. -/
theorem intervalSearchCost_log_bound (t : AugmentedRBTree Interval Nat) (q : Interval)
    (hShape : RBTree.RedBlackShape (AugmentedRBTree.toRB_low t)) :
    IntervalTree.intervalSearchCost (AugmentedRBTree.toIntervalTree t) q ≤
      2 * Nat.log 2 (RBTree.size (AugmentedRBTree.toRB_low t) + 1) + 1 := by
  have hh := RBTree.height_log_bound (AugmentedRBTree.toRB_low t) hShape
  have hc := IntervalTree.intervalSearchCost_le_height (AugmentedRBTree.toIntervalTree t) q
  rw [AugmentedRBTree.intervalHeight_eq_toRB_height t] at hc
  omega

end Chapter14
end CLRS
