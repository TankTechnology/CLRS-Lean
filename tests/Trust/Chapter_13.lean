import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_13

/-! # Chapter 13 flagship trust surface -/

#check CLRS.Chapter13.RBTree.insert_correct
#check CLRS.Chapter13.RBTree.delete_correct
#check CLRS.Chapter13.RBTree.height_log_bound

#assert_axioms CLRS.Chapter13.RBTree.insert_correct
#assert_axioms CLRS.Chapter13.RBTree.delete_correct
#assert_axioms CLRS.Chapter13.RBTree.height_log_bound

example :
    CLRS.Chapter13.RBTree.InTree 3
      (CLRS.Chapter13.RBTree.insert 3 CLRS.Chapter13.RBTree.empty) := by
  simp [CLRS.Chapter13.RBTree.insert, CLRS.Chapter13.RBTree.insertFixup,
    CLRS.Chapter13.RBTree.repaintRoot, CLRS.Chapter13.RBTree.InTree]

#check CLRS.Chapter13.StoreReprAt.unique
#assert_axioms CLRS.Chapter13.StoreReprAt.unique
#check CLRS.Chapter13.Represents.tree_unique
#assert_axioms CLRS.Chapter13.Represents.tree_unique
#check CLRS.Chapter13.rotateLeftP_refines_root
#assert_axioms CLRS.Chapter13.rotateLeftP_refines_root
#check CLRS.Chapter13.rotateRightP_refines_root
#assert_axioms CLRS.Chapter13.rotateRightP_refines_root
#check CLRS.Chapter13.rotateLeftP_refines_context
#assert_axioms CLRS.Chapter13.rotateLeftP_refines_context
#check CLRS.Chapter13.rotateRightP_refines_context
#assert_axioms CLRS.Chapter13.rotateRightP_refines_context
#check CLRS.Chapter13.rotateLeftP_missing
#assert_axioms CLRS.Chapter13.rotateLeftP_missing
#check CLRS.Chapter13.rotateRightP_missing
#assert_axioms CLRS.Chapter13.rotateRightP_missing
