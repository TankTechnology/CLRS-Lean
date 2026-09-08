import CLRSLean.FourthEdition.Chapter_17.Section_17_3_Interval_Trees

open CLRS.Chapter14
local instance : DecidableEq Interval := inferInstanceAs (DecidableEq (Nat × Nat))

#check AugmentedRBTree.mem_keys_insert_of_compare
#check AugmentedRBTree.ordered_insert
#check AugmentedRBTree.intervalLt_separates
#check AugmentedRBTree.mem_keys_interval_insert
#check AugmentedRBTree.intervalBST_insert
#check AugmentedRBTree.isBST_toIntervalTree_insert
#check intervalSearch_insert_spec
#check intervalSearch_insert_finds

private def initial : AugmentedRBTree Interval Nat :=
  .node .black .empty (0, 1) 1 .empty
private def updated :=
  AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt (0, 10) initial

-- The audited same-low counterexample now retains both complete intervals.
example : AugmentedRBTree.keys updated = [(0, 1), (0, 10)] := by decide
example : (0, 10) ∈ AugmentedRBTree.keys updated := by decide
example : IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree updated) (5, 5) = some (0, 10) := by decide
example : IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree updated) (20, 20) = none := by decide

-- Comparator ties identify complete intervals, not just their low endpoints.
example : AugmentedRBTree.intervalLt (0, 1) (0, 10) = true := rfl
example : AugmentedRBTree.intervalLt (0, 10) (0, 1) = false := rfl
example : AugmentedRBTree.intervalLt (0, 10) (0, 10) = false := rfl
example : AugmentedRBTree.intervalLt (0, 100) (1, 0) = true := rfl
example : AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt (0, 1) initial = initial := rfl

private theorem initial_augmented : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug initial := by
  simp [initial, AugmentedRBTree.WellAugmented, AugmentedRBTree.realAug,
    IntervalTree.maxHighAug, Interval.high]

private theorem initial_bst : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree initial) := by
  simp [initial, AugmentedRBTree.toIntervalTree, IntervalTree.IsBST, IntervalTree.allLowLE,
    IntervalTree.allLowGE, IntervalTree.keys, AugmentedTree.keys]

private theorem initial_lex_bst : AugmentedRBTree.IntervalBST initial := by
  simp [initial, AugmentedRBTree.IntervalBST, AugmentedRBTree.Ordered, AugmentedRBTree.keys]

-- The corrected behavior also follows from the general verified update bridge.
example : ∃ i, IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree updated) (5, 5) = some i ∧
    (i = (0, 10) ∨ i ∈ AugmentedRBTree.keys initial) ∧ Interval.overlaps i (5, 5) = true :=
  intervalSearch_insert_finds (0, 10) (5, 5) initial_bst initial_augmented (by decide)

example : AugmentedRBTree.IntervalBST updated :=
  AugmentedRBTree.intervalBST_insert (0, 10) initial_lex_bst
example : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree updated) :=
  AugmentedRBTree.isBST_toIntervalTree_insert (0, 10) initial_bst

-- Repeated updates exercise rebalancing and both comparison directions.
private def add (t : AugmentedRBTree Interval Nat) (i : Interval) :=
  AugmentedRBTree.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt i t
private def many := ([(0, 10), (0, 1), (0, 5), (3, 8), (7, 9), (0, 10)] : List Interval).foldl add .empty

example : AugmentedRBTree.keys many = [(0, 1), (0, 5), (0, 10), (3, 8), (7, 9)] := by decide
example : IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree many) (6, 6) ≠ none := by decide
example : IntervalTree.intervalSearch? (AugmentedRBTree.toIntervalTree many) (12, 12) = none := by decide

-- Member preservation is independent of augmentation correctness or BST shape.
example (q i : Interval) (t : AugmentedRBTree Interval Nat) :
    i ∈ AugmentedRBTree.keys (add t q) ↔ i = q ∨ i ∈ AugmentedRBTree.keys t :=
  AugmentedRBTree.mem_keys_interval_insert q i t

#print axioms AugmentedRBTree.mem_keys_interval_insert
#print axioms AugmentedRBTree.intervalBST_insert
#print axioms AugmentedRBTree.isBST_toIntervalTree_insert
#print axioms intervalSearch_insert_spec
#print axioms intervalSearch_insert_finds
