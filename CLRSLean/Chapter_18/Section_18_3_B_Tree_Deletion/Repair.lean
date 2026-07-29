import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Invariant
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Rotation

/-!
# Bundled local repair invariants for B-tree deletion

This module packages the component preservation lemmas for the three local
repairs used by {lit}`composedDelete`: merging two minimal siblings, borrowing
from a right sibling, and borrowing from a left sibling.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
Merging two minimal, equally deep siblings around their separator preserves
the complete non-root {lit}`NodeWF` packet and the height of the left sibling.
-/
theorem mergeNodes_nodeWF {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleft : NodeWF t false left) (hright : NodeWF t false right)
    (hleftKeys : numKeys left = t - 1)
    (hrightKeys : numKeys right = t - 1)
    (hheight : heightOf left = heightOf right)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    NodeWF t false (mergeNodes left sep right) ∧
      heightOf (mergeNodes left sep right) = heightOf left := by
  rcases left with ⟨lKeys, lCh⟩
  rcases right with ⟨rKeys, rCh⟩
  have hlk : lKeys.length = t - 1 := by
    simpa [numKeys] using hleftKeys
  have hrk : rKeys.length = t - 1 := by
    simpa [numKeys] using hrightKeys
  have hshape : (lCh = []) ↔ (rCh = []) :=
    leaf_iff_of_height_eq hheight
  refine ⟨?_, mergeNodes_height hleft.sameDepth hright.sameDepth hheight⟩
  exact
    ⟨mergeNodes_sorted hleft.sorted hright.sorted hleftLe hrightGe,
      mergeNodes_childBounded hleft.childBounded hright.childBounded
        hshape hleftLe hrightGe,
      mergeNodes_occupancy ht hlk hrk hleft.childBounded
        hright.childBounded hleft.occupancy hright.occupancy,
      mergeNodes_sameDepth hleft.sameDepth hright.sameDepth hheight⟩

/--
Borrowing from the right sibling preserves the complete non-root
{lit}`NodeWF` packet for both result nodes and preserves each sibling's height.
-/
theorem rotateRight_nodeWF {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleft : NodeWF t false left) (hright : NodeWF t false right)
    (hleftKeys : numKeys left = t - 1)
    (hrightKeys : t ≤ numKeys right)
    (hheight : heightOf left = heightOf right)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    let repaired := rotateRight left sep right
    NodeWF t false repaired.1 ∧ NodeWF t false repaired.2.2 ∧
      heightOf repaired.1 = heightOf left ∧
      heightOf repaired.2.2 = heightOf right := by
  rcases left with ⟨lKeys, lCh⟩
  rcases right with ⟨rKeys, rCh⟩
  have hlk : lKeys.length = t - 1 := by
    simpa [numKeys] using hleftKeys
  have hrlen : t ≤ rKeys.length := by
    simpa [numKeys] using hrightKeys
  obtain ⟨rHead, rTail, rfl⟩ : ∃ rHead rTail, rKeys = rHead :: rTail := by
    cases rKeys with
    | nil =>
        simp only [List.length_nil] at hrlen
        omega
    | cons rHead rTail =>
        exact ⟨rHead, rTail, rfl⟩
  have hshape : (lCh = []) ↔ (rCh = []) :=
    leaf_iff_of_height_eq hheight
  have hsep : sep ≤ rHead :=
    hrightGe rHead (by simp [keysOf])
  have hpreserves :=
    rotateRight_preserves (sep := sep) ht hlk hrlen hleft.childBounded
      hright.childBounded hleft.sameDepth hright.sameDepth
      hleft.occupancy hright.occupancy hheight
  have hsortedLeft :=
    rotateRight_sorted_left hleft.sorted hright.sorted hleftLe hsep
  have hboundedLeft :=
    rotateRight_childBounded_left hleft.childBounded hright.childBounded
      hshape hleftLe hrightGe
  have hsortedRight :=
    rotateRight_sorted_right hright.sorted
  have hboundedRight :=
    rotateRight_childBounded_right hright.childBounded
  simp only [rotateRight_cons] at hpreserves ⊢
  exact
    ⟨⟨hsortedLeft, hboundedLeft, hpreserves.1.1, hpreserves.1.2.1⟩,
      ⟨hsortedRight, hboundedRight, hpreserves.2.1, hpreserves.2.2.1⟩,
      hpreserves.1.2.2,
      hpreserves.2.2.2⟩

/--
Borrowing from the left sibling preserves the complete non-root
{lit}`NodeWF` packet for both result nodes and preserves each sibling's height.
-/
theorem rotateLeft_nodeWF {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleft : NodeWF t false left) (hright : NodeWF t false right)
    (hleftKeys : t ≤ numKeys left)
    (hrightKeys : numKeys right = t - 1)
    (hheight : heightOf left = heightOf right)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    let repaired := rotateLeft left sep right
    NodeWF t false repaired.1 ∧ NodeWF t false repaired.2.2 ∧
      heightOf repaired.1 = heightOf left ∧
      heightOf repaired.2.2 = heightOf right := by
  rcases left with ⟨lKeys, lCh⟩
  rcases right with ⟨rKeys, rCh⟩
  have hllen : t ≤ lKeys.length := by
    simpa [numKeys] using hleftKeys
  have hrk : rKeys.length = t - 1 := by
    simpa [numKeys] using hrightKeys
  obtain ⟨lHead, lTail, rfl⟩ : ∃ lHead lTail, lKeys = lHead :: lTail := by
    cases lKeys with
    | nil =>
        simp only [List.length_nil] at hllen
        omega
    | cons lHead lTail =>
        exact ⟨lHead, lTail, rfl⟩
  have hshape : (lCh = []) ↔ (rCh = []) :=
    leaf_iff_of_height_eq hheight
  have hpreservesLeft :=
    rotateLeft_left ht hllen hleft.childBounded
      hleft.occupancy hleft.sameDepth
  have hpreservesRight :=
    rotateLeft_right (sep := sep) ht hrk hright.childBounded hleft.sameDepth
      hright.sameDepth hleft.occupancy hright.occupancy hheight
  have hsortedLeft :=
    rotateLeft_sorted_left hleft.sorted
  have hboundedLeft :=
    rotateLeft_childBounded_left hleft.childBounded
  have hsortedRight :=
    rotateLeft_sorted_right hleft.sorted hright.sorted hleftLe hrightGe
  have hboundedRight :=
    rotateLeft_childBounded_right hleft.childBounded hright.childBounded
      hshape hleftLe hrightGe
  simp only [rotateLeft_cons] at hpreservesLeft hpreservesRight ⊢
  exact
    ⟨⟨hsortedLeft, hboundedLeft, hpreservesLeft.1, hpreservesLeft.2.1⟩,
      ⟨hsortedRight, hboundedRight, hpreservesRight.1, hpreservesRight.2.1⟩,
      hpreservesLeft.2.2,
      hpreservesRight.2.2⟩

/-! ## Readiness of repaired recursive targets -/

/--
Merging a minimal left sibling with a separator produces a non-root target
with at least {lit}`t` keys, regardless of the right sibling's key count.
-/
theorem mergeNodes_deleteReady {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleftKeys : numKeys left = t - 1) :
    DeleteReady t false (mergeNodes left sep right) := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  simp only [DeleteReady, Bool.false_eq_true, false_or, numKeys,
    mergeNodes_node, List.length_append, List.length_cons]
  change lKeys.length = t - 1 at hleftKeys
  omega

/--
Two adjacent non-ready siblings form a well-formed, ready recursive target
when merged around their separator.
-/
theorem mergeNodes_recursiveTarget {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleft : NodeWF t false left) (hright : NodeWF t false right)
    (hleftNotReady : ¬ t ≤ numKeys left)
    (hrightNotReady : ¬ t ≤ numKeys right)
    (hheight : heightOf left = heightOf right)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    NodeWF t false (mergeNodes left sep right) ∧
      DeleteReady t false (mergeNodes left sep right) ∧
      heightOf (mergeNodes left sep right) = heightOf left := by
  have hleftMin : numKeys left = t - 1 :=
    numKeys_eq_t_sub_one_of_not_ready hleft.occupancy hleftNotReady
  have hrightMin : numKeys right = t - 1 :=
    numKeys_eq_t_sub_one_of_not_ready hright.occupancy hrightNotReady
  have hmerged :=
    mergeNodes_nodeWF ht hleft hright hleftMin hrightMin
      hheight hleftLe hrightGe
  exact
    ⟨hmerged.1, mergeNodes_deleteReady ht hleftMin, hmerged.2⟩

/--
After borrowing from the right, the repaired left child has at least {lit}`t`
keys and is ready for recursive deletion.
-/
theorem rotateRight_repaired_deleteReady {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleftKeys : numKeys left = t - 1)
    (hrightKeys : t ≤ numKeys right) :
    DeleteReady t false (rotateRight left sep right).1 := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  change lKeys.length = t - 1 at hleftKeys
  change t ≤ rKeys.length at hrightKeys
  obtain ⟨rHead, rTail, rfl⟩ : ∃ rHead rTail, rKeys = rHead :: rTail := by
    cases rKeys with
    | nil =>
        simp only [List.length_nil] at hrightKeys
        omega
    | cons rHead rTail =>
        exact ⟨rHead, rTail, rfl⟩
  simp only [DeleteReady, Bool.false_eq_true, false_or, rotateRight_cons,
    numKeys, List.length_append, List.length_cons, List.length_nil]
  omega

/--
After borrowing from the left, the repaired right child has at least {lit}`t`
keys and is ready for recursive deletion.
-/
theorem rotateLeft_repaired_deleteReady {t : Nat} (ht : 2 ≤ t)
    {left right : BTree} {sep : Nat}
    (hleftKeys : t ≤ numKeys left)
    (hrightKeys : numKeys right = t - 1) :
    DeleteReady t false (rotateLeft left sep right).2.2 := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  change t ≤ lKeys.length at hleftKeys
  change rKeys.length = t - 1 at hrightKeys
  obtain ⟨lHead, lTail, rfl⟩ : ∃ lHead lTail, lKeys = lHead :: lTail := by
    cases lKeys with
    | nil =>
        simp only [List.length_nil] at hleftKeys
        omega
    | cons lHead lTail =>
        exact ⟨lHead, lTail, rfl⟩
  simp only [DeleteReady, Bool.false_eq_true, false_or, rotateLeft_cons,
    numKeys, List.length_cons]
  omega

end BTree
end Chapter18
end CLRS
