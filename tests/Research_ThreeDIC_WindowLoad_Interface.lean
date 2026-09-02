import CLRSLean.Research.ThreeDIC.WindowLoad

open CLRS.Research.ThreeDIC

#check windowIndexPoint
#check windowIndexPoint_inWindow
#check windowIndexPoint_injective
#check exists_windowIndexPoint_eq
#check windowColorCount
#check affineChainColor_window_count_eq_floor_or_ceil
#check affineChainColor_window_load_le_ceilDiv

example : windowColorCount 3 8 0 0 0 = 2 := by decide

example : windowColorCount 3 8 1 2 0 ≤ 2 := by decide
