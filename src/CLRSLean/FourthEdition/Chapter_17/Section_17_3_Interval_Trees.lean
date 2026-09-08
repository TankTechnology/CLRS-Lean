import Mathlib
import CLRSLean.FourthEdition.Chapter_17.Section_17_3_Interval_Trees.Insertion

/-!
# Section 17.3 — Interval trees

Interval insertion compares both endpoints lexicographically, retaining distinct
intervals with equal low endpoints. The generic insertion companion proves
complete-key membership and preservation of compatible transitive orderings.
Its interval instance preserves strict lexicographic BST order and the weaker
low-endpoint ordering used by the static search algorithm.

Color erasure preserves keys, max-high augmentation, and the static BST
predicate. {lit}`intervalSearch_insert_spec` derives both post-insertion
invariants from the input and proves complete search over the enlarged interval
set: a failed search means neither the inserted interval nor any old interval
overlaps the query. A successful search returns an old or newly inserted key
that overlaps. {lit}`intervalSearch_insert_finds` guarantees success whenever
the newly inserted interval overlaps the query.

The historical {lit}`intervalSearch_after_update` theorem remains the
augmentation-only part of that bridge. The search-height analysis uses a
conservative descent budget, which continues its accounting after a root match;
its logarithmic bound assumes the supplied red-black shape invariant. These
search results do not constitute a new red-black shape-preservation theorem for
the interval insertion pipeline.
-/

namespace CLRS
namespace Chapter14

namespace IntervalTree

/-- The height of an interval tree (maximum depth of the augmented tree). -/
def intervalHeight : IntervalTree → Nat
  | AugmentedTree.empty => 0
  | AugmentedTree.node l _ _ r => 1 + max (intervalHeight l) (intervalHeight r)

/-- Conservative descent budget for {lit}`intervalSearch?`: one node per
level, continuing the accounting even when a matching interval stops search. -/
def intervalSearchCost : IntervalTree → Interval → Nat
  | AugmentedTree.empty, _ => 0
  | AugmentedTree.node l _ _ r, q =>
      1 + if goLeft l q then intervalSearchCost l q else intervalSearchCost r q

/-- The conservative interval-search descent budget is bounded by height plus one. -/
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

/-- The augmentation part of the insertion bridge. The stronger
{lit}`intervalSearch_insert_spec` below also derives BST preservation and
search correctness from the input invariants. -/
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
augmented red-black tree with {lit}`n` nodes, the conservative search descent budget is at most
{lit}`2 log₂(n+1) + 1` node visits, composing
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

namespace AugmentedRBTree

/-- Color erasure preserves every complete interval key. -/
theorem keys_toIntervalTree (t : AugmentedRBTree Interval Nat) :
    IntervalTree.keys (toIntervalTree t) = keys t := by
  induction t with
  | empty => rfl
  | node c l k a r ihl ihr =>
    simp only [toIntervalTree, IntervalTree.keys_node, keys, ihl, ihr]

/-- The static search BST predicate is exactly weak inorder low ordering. -/
theorem isBST_toIntervalTree_iff (t : AugmentedRBTree Interval Nat) :
    IntervalTree.IsBST (toIntervalTree t) ↔ LowOrdered t := by
  induction t with
  | empty => simp [toIntervalTree, IntervalTree.IsBST, LowOrdered, Ordered, keys]
  | node c l k a r ihl ihr =>
    rw [show LowOrdered (.node c l k a r) ↔
      LowOrdered l ∧ LowOrdered r ∧ (∀ i ∈ keys l, i.low ≤ k.low) ∧
      (∀ i ∈ keys r, k.low ≤ i.low) from
      ordered_node (fun i j : Interval => i.low ≤ j.low) (fun _ _ _ => le_trans) c l k a r]
    simp only [toIntervalTree, IntervalTree.IsBST, ihl, ihr, IntervalTree.allLowLE,
      IntervalTree.allLowGE, keys_toIntervalTree]

/-- Insertion preserves the precise BST premise needed by static interval search. -/
theorem isBST_toIntervalTree_insert (q : Interval) {t : AugmentedRBTree Interval Nat}
    (h : IntervalTree.IsBST (toIntervalTree t)) :
    IntervalTree.IsBST (toIntervalTree (insert IntervalTree.maxHighAug intervalLt q t)) :=
  (isBST_toIntervalTree_iff _).mpr (lowOrdered_insert q ((isBST_toIntervalTree_iff t).mp h))

/-- Strict lexicographic interval BSTs satisfy the static search ordering. -/
theorem IntervalBST.toIntervalTree {t : AugmentedRBTree Interval Nat} (h : IntervalBST t) :
    IntervalTree.IsBST (toIntervalTree t) :=
  (isBST_toIntervalTree_iff t).mpr h.lowOrdered

/-- Overlaps after insertion are exactly the new interval's overlaps plus old ones. -/
theorem hasOverlap_interval_insert (q query : Interval) (t : AugmentedRBTree Interval Nat) :
    IntervalTree.hasOverlap (toIntervalTree (insert IntervalTree.maxHighAug intervalLt q t)) query ↔
      Interval.overlaps q query = true ∨ IntervalTree.hasOverlap (toIntervalTree t) query := by
  simp only [IntervalTree.hasOverlap, keys_toIntervalTree, mem_keys_interval_insert]
  constructor
  · rintro ⟨i, hi, hov⟩
    rcases hi with rfl | hi
    · exact Or.inl hov
    · exact Or.inr ⟨i, hi, hov⟩
  · rintro (hq | ⟨i, hi, hov⟩)
    · exact ⟨q, Or.inl rfl, hq⟩
    · exact ⟨i, Or.inr hi, hov⟩

end AugmentedRBTree

/-- Search after actual insertion is complete for the enlarged interval set
and returns only a stored overlapping interval. Both input invariants are
explicit, and their postconditions are derived from the insertion execution. -/
theorem intervalSearch_insert_spec (q query : Interval) {t : AugmentedRBTree Interval Nat}
    (hB : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree t))
    (hW : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug t) :
    let updated := AugmentedRBTree.toIntervalTree
      (AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt q t)
    (IntervalTree.intervalSearch? updated query = none ↔
      ¬ (Interval.overlaps q query = true ∨ IntervalTree.hasOverlap (AugmentedRBTree.toIntervalTree t) query)) ∧
    (∀ i, IntervalTree.intervalSearch? updated query = some i →
      (i = q ∨ i ∈ AugmentedRBTree.keys t) ∧ Interval.overlaps i query = true) := by
  have hs := IntervalTree.intervalSearch?_spec
    (AugmentedRBTree.isBST_toIntervalTree_insert q hB) (intervalSearch_after_update q hW) query
  simpa only [AugmentedRBTree.hasOverlap_interval_insert, AugmentedRBTree.keys_toIntervalTree,
    AugmentedRBTree.mem_keys_interval_insert] using hs

/-- An inserted interval overlapping the query guarantees a successful search. -/
theorem intervalSearch_insert_finds (q query : Interval) {t : AugmentedRBTree Interval Nat}
    (hB : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree t))
    (hW : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug t)
    (hq : Interval.overlaps q query = true) :
    ∃ i, IntervalTree.intervalSearch?
      (AugmentedRBTree.toIntervalTree
        (AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt q t)) query = some i ∧
      (i = q ∨ i ∈ AugmentedRBTree.keys t) ∧ Interval.overlaps i query = true := by
  have hs := intervalSearch_insert_spec q query hB hW
  have hn : IntervalTree.intervalSearch?
      (AugmentedRBTree.toIntervalTree
        (AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt q t)) query ≠ none := by
    intro he
    exact hs.1.mp he (Or.inl hq)
  obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hn
  exact ⟨i, hi, hs.2 i hi⟩


end Chapter14
end CLRS
