import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_17.Section_17_2_Augmenting_Data_Structures.Execution

open CLRS.Chapter14 CLRS.Chapter13
open AugmentationExecution

#check insert_refines
#check insert_toRB
#check insert_wellAugmented
#check insert_counts
#check insert_combineCalls_log_bound
#check insert_rotations_log_bound
#check insert_maintenanceCost_log_bound
#assert_axioms insert_refines
#assert_axioms insert_toRB
#assert_axioms insert_wellAugmented
#assert_axioms rotateLeft_counts
#assert_axioms rotateRight_counts
#assert_axioms rotateLeft_wellAugmented
#assert_axioms rotateRight_wellAugmented
#assert_axioms rotateLeft_toRB
#assert_axioms rotateRight_toRB
#assert_axioms insert_counts
#assert_axioms insert_maintenanceCost_log_bound

private def leaf (c : Color) (x : Nat) : AugmentedRBTree Nat Nat :=
  .node c .empty x 1 .empty
private def leftSeed : AugmentedRBTree Nat Nat :=
  .node .black (leaf .red 1) 3 2 .empty
private def rightSeed : AugmentedRBTree Nat Nat :=
  .node .black .empty 1 2 (leaf .red 3)
private def run := insert (sizeAug Nat) AugmentedRBTree.natLt

example : (run 0 leftSeed).combineCalls = 5 ∧ (run 0 leftSeed).rotations = 1 := by decide
example : (run 2 leftSeed).combineCalls = 7 ∧ (run 2 leftSeed).rotations = 2 := by decide
example : (run 2 rightSeed).combineCalls = 7 ∧ (run 2 rightSeed).rotations = 2 := by decide
example : (run 4 rightSeed).combineCalls = 5 ∧ (run 4 rightSeed).rotations = 1 := by decide
example : (run 3 leftSeed).combineCalls = 0 ∧ (run 3 leftSeed).rotations = 0 ∧
    (run 3 leftSeed).tree = leftSeed := by decide
example : (run 1 .empty).combineCalls = 1 ∧ (run 1 .empty).rotations = 0 ∧
    (run 1 .empty).tree = leaf .black 1 := by decide

example : AugmentedRBTree.WellAugmented (sizeAug Nat) leftSeed := by
  simp [leftSeed, leaf, AugmentedRBTree.WellAugmented, AugmentedRBTree.realAug, sizeAug]
example : (run 2 leftSeed).tree =
    AugmentedRBTree.insert (sizeAug Nat) AugmentedRBTree.natLt 2 leftSeed := by decide
example : AugmentedRBTree.storedAug (sizeAug Nat) (run 2 leftSeed).tree = 3 := by decide

-- Successful primitives each perform exactly two local recomputations.
example : (rotateLeft (sizeAug Nat) (pure rightSeed)).combineCalls = 2 ∧
    (rotateLeft (sizeAug Nat) (pure rightSeed)).rotations = 1 := by decide
example : (rotateRight (sizeAug Nat) (pure leftSeed)).combineCalls = 2 ∧
    (rotateRight (sizeAug Nat) (pure leftSeed)).rotations = 1 := by decide
example : (rotateRight (sizeAug Nat) (pure rightSeed)).combineCalls = 0 ∧
    (rotateRight (sizeAug Nat) (pure rightSeed)).rotations = 0 := by decide

-- Cached reads are observable: this deliberately invalid cache is not traversed/repaired.
example : AugmentedRBTree.storedAug (sizeAug Nat)
    (make (sizeAug Nat) .black
      (pure (.node .black .empty 1 99 .empty)) 2 (pure .empty)).tree = 100 := by decide

example (aug : Augmentation Nat Nat) (t : AugmentedRBTree Nat Nat)
    (h : AugmentedRBTree.WellAugmented aug t) (x : Nat) :
    AugmentedRBTree.toRB (insert aug AugmentedRBTree.natLt x t).tree =
      RBTree.insert x (AugmentedRBTree.toRB t) := insert_toRB aug x t h
