import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_16

/-! # Chapter 16 flagship trust surface -/

#check CLRS.Chapter17.multiPop_totalCost_le
#check CLRS.Chapter17.binaryCounter_trace_totalFlips_le
#check CLRS.Chapter17.trace_totalCost_le_three_mul

#assert_axioms CLRS.Chapter17.multiPop_totalCost_le
#assert_axioms CLRS.Chapter17.binaryCounter_trace_totalFlips_le
#assert_axioms CLRS.Chapter17.trace_totalCost_le_three_mul

example : CLRS.Chapter17.multiPop [1, 2, 3] 2 = [3] := by
  decide
