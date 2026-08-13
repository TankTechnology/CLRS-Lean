import Mathlib
import CLRSLean.Chapter_14.Section_14_3_Interval_Trees
import CLRSLean.FourthEdition.Chapter_13.Section_13_4_Deletion

/-!
# Section 17.2 - How to augment a data structure

This section closes the fourth-edition §17.2 boundary.  The legacy
{lit}`CLRSLean.Chapter_14` development already proves the *maintainability* of an
augmentation — {lit}`AugmentedTree.augmentation_theorem` and
{lit}`AugmentedRBTree.wellAugmented_insert` show that a rotation-invariant,
locally-recomputed field survives every red-black primitive.  What remains is
the **cost** of that maintenance: CLRS §17.2's asymptotic bound that a
constant-time `combine` makes the whole update {lit}`O(log n)`.

We formalize the constant-time premise (the `combine` call costs a fixed number
{lit}`c` of pointer operations) and prove that the augmentation maintenance cost
of a red-black update is {lit}`c` times the length of the {lit}`O(log n)` fixup
path.

Main results:

- Definition {lit}`augmentationUpdateCost`: the augmentation maintenance cost of
  a red-black update (a constant `combine` cost per node on the fixup path).
- Theorem {lit}`augmentation_update_bound`: **from a constant-time `combine`,
  augmentation maintenance during a red-black update is {lit}`O(log n)`**.
-/

namespace CLRS
namespace Chapter14

open CLRS.Chapter13 (RBTree)
open AugmentedRBTree (toRB)

/-- The augmentation maintenance cost of a red-black update on
{lit}`AugmentedRBTree`: the number of `combine` recomputations on the
{lit}`O(log n)` search-and-fixup path, each costing the constant `c`. -/
def augmentationUpdateCost (c : Nat) {β : Type} (t : AugmentedRBTree Nat β) : Nat :=
  c * (RBTree.height (toRB t) + 1)

/-- **CLRS §17.2 augmentation update bound.**  From the constant-time `combine`
premise (cost `c` per call), the augmentation maintenance cost of a red-black
update is {lit}`O(log n)`: at most {lit}`c · (2 log₂(n+1) + 1)` pointer
operations on a red-black-shaped tree with {lit}`n` nodes. -/
theorem augmentation_update_bound (c : Nat) {β : Type} (t : AugmentedRBTree Nat β)
    (hShape : RBTree.RedBlackShape (toRB t)) :
    augmentationUpdateCost c t ≤ c * (2 * Nat.log 2 (RBTree.size (toRB t) + 1) + 1) := by
  simp only [augmentationUpdateCost]
  have hh := RBTree.height_log_bound (toRB t) hShape
  exact Nat.mul_le_mul_left c (Nat.add_le_add_right hh 1)

end Chapter14
end CLRS
