import Mathlib
import CLRSLean.Chapter_14.Section_14_1_Order_Statistic_Trees
import CLRSLean.FourthEdition.Chapter_13.Section_13_3_Insertion

/-!
# Section 17.1 - Dynamic order statistics

This section completes the fourth-edition §17.1 boundary for dynamic
order-statistic trees.  The legacy {lit}`CLRSLean.Chapter_14` development
already provides OS-SELECT ({lit}`OSRBTree.osSelect?`) and the subtree-size
augmentation through executable red-black insertion and deletion.  The missing
operation is **OS-RANK** — given a key, return its rank (the number of stored
keys strictly smaller than it).

We add {lit}`OSRBTree.osRank` (using cached sizes) and the ideal
{lit}`OSRBTree.rankOf` (using recomputed sizes), prove they agree on well-sized
trees, and prove OS-RANK runs in {lit}`O(log n)` pointer operations via the
height of the underlying red-black tree.

Main results:

- Definition {lit}`OSRBTree.osRank` / {lit}`OSRBTree.rankOf`: OS-RANK with cached
  and recomputed sizes.
- Theorem {lit}`OSRBTree.osRank_eq_rankOf_of_wellSized`: cached and ideal ranks
  agree on well-sized trees.
- Theorem {lit}`OSRBTree.osRankCost_le_height`: the pointer cost of OS-RANK is
  bounded by the tree height.
- Theorem {lit}`OSRBTree.osRankCost_log_bound`: **OS-RANK runs in
  {lit}`O(log n)`** on a red-black-shaped tree.
-/

namespace CLRS
namespace Chapter14
namespace OSRBTree

open CLRS.Chapter13 (RBTree)

/-! ## OS-RANK -/

/-- The ideal rank of `x`: the number of stored keys strictly smaller than `x`,
computed with recomputed (mathematical) subtree sizes. -/
def rankOf : OSRBTree → Nat → Nat
  | empty, _ => 0
  | node _ l k _ r, x =>
      if x < k then rankOf l x
      else if x > k then realSize l + 1 + rankOf r x
      else realSize l

/-- OS-RANK using the cached size fields. -/
def osRank : OSRBTree → Nat → Nat
  | empty, _ => 0
  | node _ l k _ r, x =>
      if x < k then osRank l x
      else if x > k then storedSize l + 1 + osRank r x
      else storedSize l

/-- The pointer-operation cost of OS-RANK: one node read per level of the
descent (a root-to-leaf path). -/
def osRankCost : OSRBTree → Nat → Nat
  | empty, _ => 0
  | node _ l k _ r, x =>
      if x < k then 1 + osRankCost l x
      else if x > k then 1 + osRankCost r x
      else 1

/-- The cached OS-RANK agrees with the ideal rank on well-sized trees. -/
theorem osRank_eq_rankOf_of_wellSized {t : OSRBTree} {x : Nat}
    (h : WellSized t) : osRank t x = rankOf t x := by
  induction t generalizing x with
  | empty => rfl
  | node c l k s r ihl ihr =>
    obtain ⟨hL, hR, _⟩ := h
    have hlSize : storedSize l = realSize l := storedSize_eq_realSize_of_wellSized hL
    by_cases hlt : x < k
    · simp [osRank, rankOf, hlt, ihl hL]
    · by_cases hgt : x > k
      · simp [osRank, rankOf, hlt, hgt, hlSize, ihr hR]
      · have heq : x = k := by omega
        simp [osRank, rankOf, hlt, hgt, heq, hlSize]

/-- Erasing the size field preserves the node count: the Chapter 13 `size` of
the erasure equals the mathematical {lit}`realSize`. -/
theorem toRB_size (t : OSRBTree) : RBTree.size (toRB t) = realSize t := by
  induction t with
  | empty => rfl
  | node c l k s r ihl ihr => simp [toRB, RBTree.size, realSize, ihl, ihr]; omega

/-- The pointer cost of OS-RANK is bounded by the height of the underlying tree. -/
theorem osRankCost_le_height (t : OSRBTree) (x : Nat) :
    osRankCost t x ≤ RBTree.height (toRB t) + 1 := by
  induction t generalizing x with
  | empty => simp [osRankCost, toRB, RBTree.height]
  | node c l k s r ihl ihr =>
    simp only [osRankCost, toRB, RBTree.height]
    by_cases hlt : x < k
    · simp [hlt]
      have ih := ihl x
      have hmax : RBTree.height (toRB l) ≤ max (RBTree.height (toRB l)) (RBTree.height (toRB r)) :=
        Nat.le_max_left _ _
      omega
    · by_cases hgt : x > k
      · simp [hlt, hgt]
        have ih := ihr x
        have hmax : RBTree.height (toRB r) ≤ max (RBTree.height (toRB l)) (RBTree.height (toRB r)) :=
          Nat.le_max_right _ _
        omega
      · simp [hlt, hgt]

/-- **OS-RANK runs in {lit}`O(log n)`.**  On a red-black-shaped tree with
{lit}`n` nodes, OS-RANK performs at most {lit}`2 log₂(n+1) + 1` pointer
operations. -/
theorem osRankCost_log_bound (t : OSRBTree) (x : Nat)
    (hShape : RBTree.RedBlackShape (toRB t)) :
    osRankCost t x ≤ 2 * Nat.log 2 (realSize t + 1) + 1 := by
  have hh := RBTree.height_log_bound (toRB t) hShape
  have hc := osRankCost_le_height t x
  rw [toRB_size t] at hh
  omega

end OSRBTree
end Chapter14
end CLRS
