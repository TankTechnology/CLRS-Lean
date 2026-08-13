import Mathlib
import CLRSLean.FourthEdition.Chapter_13.Section_13_3_Insertion

/-!
# Section 13.4 - Deletion

This section closes the fourth-edition §13.4 boundary for red-black deletion.
The legacy functional {lit}`RBTree.delete` already preserves membership
({lit}`inTree_delete_iff`) and red-black shape ({lit}`redBlackShape_delete`).
Here we add the remaining **logarithmic execution-cost** layer.

The composed deletion {lit}`RBTree.delete` = {lit}`repaintRoot black (del x t)`:
{lit}`del` searches down the tree, then at the deletion point applies
{lit}`join`, which removes the minimum of the right subtree via {lit}`splitMin`
and rebalances with {lit}`baldL`/`baldR`.  Every one of these stages touches at
most a root-to-leaf path, so the whole operation is {lit}`O(height)` pointer
operations.

Main results:

- Definition {lit}`RBTree.deleteCost`: the auditable pointer-operation cost of
  {lit}`RB-DELETE` (one node read and one comparison per search level, plus the
  {lit}`join`/`splitMin`/rebalance work bounded by the heights of the two
  subtrees).
- Theorem {lit}`RBTree.deleteCost_le`: the deletion cost is bounded by
  {lit}`4 * height + 1`.
- Theorem {lit}`RBTree.deleteCost_log_bound`: **RB-DELETE runs in
  {lit}`O(log n)` pointer operations** on a red-black tree.

Current gaps: the separate {lit}`BST` ordering preservation of the composed
{lit}`delete` ({lit}`bst_delete`) remains; {lit}`bst_insert` (§13.3) and the
rotation-level {lit}`bst_rotateLeft`/`bst_rotateRight` (§13.2) already cover the
insertion and rotation sides of the ordering refinement.
-/

namespace CLRS
namespace Chapter13
namespace RBTree

/-! ## Pointer-operation cost of RB-DELETE -/

/-- The pointer-operation cost of deleting `x`: one node read and one comparison
per level of the descent, plus — at the deletion point — the cost of joining the
two subtrees (removing the minimum of the right subtree and rebalancing), which
is bounded by the sum of the two subtree heights. -/
def deleteCost (x : Nat) : RBTree → Nat
  | .empty => 1
  | .node _ l y r =>
      if x < y then 2 + deleteCost x l
      else if y < x then 2 + deleteCost x r
      else 2 + height l + height r

/-- The deletion cost is bounded by {lit}`4 * height + 1`. -/
theorem deleteCost_le (x : Nat) (t : RBTree) : deleteCost x t ≤ 4 * height t + 1 := by
  induction t with
  | empty => simp [deleteCost, height]
  | node c l y r ihl ihr =>
    simp only [deleteCost, height]
    by_cases h1 : x < y
    · simp [h1]
      have hmax : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
      omega
    · by_cases h2 : y < x
      · simp [h1, h2]
        have hmax : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        omega
      · simp [h1, h2]
        have hmaxl : height l ≤ max (height l) (height r) := Nat.le_max_left _ _
        have hmaxr : height r ≤ max (height l) (height r) := Nat.le_max_right _ _
        omega

/-- **RB-DELETE runs in {lit}`O(log n)` pointer operations.**  On a
red-black-shaped tree with {lit}`n` internal nodes, deletion performs at most
{lit}`4 · (2 log₂(n+1)) + 1` pointer operations. -/
theorem deleteCost_log_bound (x : Nat) (t : RBTree) (hShape : RedBlackShape t) :
    deleteCost x t ≤ 4 * (2 * Nat.log 2 (size t + 1)) + 1 := by
  have hh := height_log_bound t hShape
  have hc := deleteCost_le x t
  omega

end RBTree
end Chapter13
end CLRS
