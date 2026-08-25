import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_18

/-! # Chapter 18 flagship trust surface -/

#check CLRS.Chapter18.BTree.insertRoot_correct
#check CLRS.Chapter18.BTree.composedDeleteRoot_correct
#check CLRS.Chapter18.BTree.diskAccessBound_isBigO_log_t

#assert_axioms CLRS.Chapter18.BTree.insertRoot_correct
#assert_axioms CLRS.Chapter18.BTree.composedDeleteRoot_correct
#assert_axioms CLRS.Chapter18.BTree.diskAccessBound_isBigO_log_t

example : CLRS.Chapter18.BTree.searchExec 10 (.node [10] []) = true := by
  rw [CLRS.Chapter18.BTree.searchExec.eq_def]
  norm_num
