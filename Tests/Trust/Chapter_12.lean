import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_12

/-! # Chapter 12 flagship trust surface -/

#check CLRS.Chapter12.BSTree.insert_ordered
#check CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete
#check CLRS.Chapter12.BSTree.expected_depth_le_O_log
#check CLRS.Chapter12.BSTree.height_buildFromPerm_eq_treapHeight
#check CLRS.Chapter12.BSTree.expected_height_le_O_log

#assert_axioms CLRS.Chapter12.BSTree.insert_ordered
#assert_axioms CLRS.Chapter12.BSTree.deleteViaTransplant_eq_delete
#assert_axioms CLRS.Chapter12.BSTree.expected_depth_le_O_log
#assert_axioms CLRS.Chapter12.BSTree.height_buildFromPerm_eq_treapHeight
#assert_axioms CLRS.Chapter12.BSTree.expected_height_le_O_log

example :
    CLRS.Chapter12.BSTree.search 3
      (CLRS.Chapter12.BSTree.insert 3 CLRS.Chapter12.BSTree.empty) = true := by
  decide
