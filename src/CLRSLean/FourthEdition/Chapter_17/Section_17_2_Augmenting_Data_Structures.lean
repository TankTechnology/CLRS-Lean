import Mathlib
import CLRSLean.Chapter_14.Section_14_3_Interval_Trees
import CLRSLean.FourthEdition.Chapter_13.Section_13_4_Deletion

/-!
# Section 17.2 - How to augment a data structure

The legacy augmentation theorems prove field correctness through functional
red-black updates. Their smart constructor recursively recomputes mathematical
child augmentations, so that implementation does not justify a local-cost claim.

The {lit}`Execution` companion supplies a distinct cached-field insertion and
rotation execution. It reads stored child fields, returns the tree plus actual
{lit}`combine` and rotation counters, and refines legacy insertion on
{lit}`WellAugmented` inputs. Insertion uses at most {lit}`5h + 1` combines and
{lit}`2h` rotations; the red-black height theorem yields logarithmic bounds.
Each executed double rotation counts both primitives and their local rebuilds.

The historical {lit}`augmentationUpdateCost` below is only an independent
height-based budget. Its theorem does not measure any update by itself. Use
{lit}`AugmentationExecution.insert_maintenanceCost_log_bound` for the executed
cached insertion. Deletion remains the legacy recomputing implementation, with
no attached logarithmic maintenance counter here. Allocation, comparison, and
bit-arithmetic internals are outside these field-maintenance counts.
-/

namespace CLRS
namespace Chapter14

open CLRS.Chapter13 (RBTree)
open AugmentedRBTree (toRB)

/-- Historical height-based analysis budget, not a measured update counter.
The cached execution companion proves its own explicit combine/rotation bounds. -/
def augmentationUpdateCost (c : Nat) {β : Type} (t : AugmentedRBTree Nat β) : Nat :=
  c * (RBTree.height (toRB t) + 1)

/-- The independent height budget is logarithmic on red-black-shaped trees.
An actual update bound requires the companion's counted-execution refinement. -/
theorem augmentation_update_bound (c : Nat) {β : Type} (t : AugmentedRBTree Nat β)
    (hShape : RBTree.RedBlackShape (toRB t)) :
    augmentationUpdateCost c t ≤ c * (2 * Nat.log 2 (RBTree.size (toRB t) + 1) + 1) := by
  simp only [augmentationUpdateCost]
  have hh := RBTree.height_log_bound (toRB t) hShape
  exact Nat.mul_le_mul_left c (Nat.add_le_add_right hh 1)

end Chapter14
end CLRS
