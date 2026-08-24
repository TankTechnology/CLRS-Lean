import CLRSLean.Chapter_34.BinaryNat

open CLRS.Chapter34
open CLRS.Chapter34.Turing.BinaryNat

#check Comparator.leWords_eq_decide
#check Comparator.leWords_eq_true_iff
#check Comparator.leWords_encoded_eq_true_iff
#check Comparator.computableInPolyTime

example :
    Comparator.leWords [false, false, true, false, true]
      [true, true, false] = true := by
  native_decide

example :
    Comparator.leWords (encodeBinaryNat 13) (encodeBinaryNat 8) = false := by
  native_decide

#print axioms Comparator.leWords_eq_true_iff
#print axioms Comparator.computableInPolyTime
