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
