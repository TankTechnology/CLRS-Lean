import CLRSLean.FourthEdition.Chapter_28

/-! # Chapter 28 executable LUP concrete regressions -/

open Matrix
open CLRS.Chapter28

example :
    (lupDecomposeWithCost 2 (!![(0 : Rat), 1; 1, 0])).result.isSome := by
  native_decide

example :
    (lupDecomposeWithCost 2 (!![(0 : Rat), 0; 0, 0])).result = none := by
  native_decide
