import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_17

/-! # Chapter 17 flagship trust surface -/

#check CLRS.Chapter14.OSRBTree.osRank_eq_rankOf_of_wellSized
#check CLRS.Chapter14.augmentation_update_bound
#check CLRS.Chapter14.intervalSearchCost_log_bound

#assert_axioms CLRS.Chapter14.OSRBTree.osRank_eq_rankOf_of_wellSized
#assert_axioms CLRS.Chapter14.augmentation_update_bound
#assert_axioms CLRS.Chapter14.intervalSearchCost_log_bound

example :
    CLRS.Chapter14.OSRBTree.osRank
      (.node .black .empty 3 1 .empty) 4 = 1 := by
  decide

#check CLRS.Chapter14.OSRBTree.rankOf_eq_card_lt
#assert_axioms CLRS.Chapter14.OSRBTree.rankOf_eq_card_lt
#check CLRS.Chapter14.OSRBTree.osRank_eq_card_lt
#assert_axioms CLRS.Chapter14.OSRBTree.osRank_eq_card_lt
#check CLRS.Chapter14.OSRBTree.keys_nodup_of_bst
#assert_axioms CLRS.Chapter14.OSRBTree.keys_nodup_of_bst

#check CLRS.Chapter14.AugmentationExecution.insert_refines
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_refines
#check CLRS.Chapter14.AugmentationExecution.insert_toRB
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_toRB
#check CLRS.Chapter14.AugmentationExecution.insert_wellAugmented
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_wellAugmented
#check CLRS.Chapter14.AugmentationExecution.insert_counts
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_counts
#check CLRS.Chapter14.AugmentationExecution.insert_combineCalls_log_bound
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_combineCalls_log_bound
#check CLRS.Chapter14.AugmentationExecution.insert_rotations_log_bound
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_rotations_log_bound
#check CLRS.Chapter14.AugmentationExecution.insert_maintenanceCost_log_bound
#assert_axioms CLRS.Chapter14.AugmentationExecution.insert_maintenanceCost_log_bound
#check CLRS.Chapter14.AugmentationExecution.rotateLeft_counts
#assert_axioms CLRS.Chapter14.AugmentationExecution.rotateLeft_counts
#check CLRS.Chapter14.AugmentationExecution.rotateRight_counts
#assert_axioms CLRS.Chapter14.AugmentationExecution.rotateRight_counts

#check CLRS.Chapter14.AugmentedRBTree.mem_keys_interval_insert
#assert_axioms CLRS.Chapter14.AugmentedRBTree.mem_keys_interval_insert
#check CLRS.Chapter14.AugmentedRBTree.intervalBST_insert
#assert_axioms CLRS.Chapter14.AugmentedRBTree.intervalBST_insert
#check CLRS.Chapter14.AugmentedRBTree.isBST_toIntervalTree_insert
#assert_axioms CLRS.Chapter14.AugmentedRBTree.isBST_toIntervalTree_insert
#check CLRS.Chapter14.intervalSearch_insert_spec
#assert_axioms CLRS.Chapter14.intervalSearch_insert_spec
#check CLRS.Chapter14.intervalSearch_insert_finds
#assert_axioms CLRS.Chapter14.intervalSearch_insert_finds
#check CLRS.Chapter14.intervalSearch_cachedInsert_spec
#assert_axioms CLRS.Chapter14.intervalSearch_cachedInsert_spec
