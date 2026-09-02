import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check bitReverseEquiv
#check bitReverseEquiv_even
#check bitReverseEquiv_odd
#check bitReverseEquiv_testBit
#check bitReverseEquiv_involutive
#check BitReverseExecution
#check bitReverseExec
#check bitReverseCopy
#check bitReverseCopy_apply
#check bitReverseCopy_involutive
#check bitReverseExec_moves

example : (bitReverseEquiv 3 ⟨1, by norm_num⟩).1 = 4 := by native_decide
example : (bitReverseEquiv 3 ⟨3, by norm_num⟩).1 = 6 := by native_decide

end CLRS.Chapter30
