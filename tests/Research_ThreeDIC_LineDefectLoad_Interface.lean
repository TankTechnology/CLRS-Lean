import CLRSLean.Research.ThreeDIC.LineDefectLoad

/-!
# Research interface: finite-prefix line-defect load bounds
-/

open CLRS.Research.ThreeDIC

#check lineColorIndices
#check lineColor_load_le_ceilDiv_period
#check lineColor_horizontal_load_le
#check lineColor_vertical_load_le
#check lineColor_coprime_load_le
#check lineColor_finiteGrid_load_le

example : (lineColorIndices 3 8 0 0 (0, 0) (1, 0)).card = 0 := by decide

example : (lineColorIndices 3 8 17 0 (0, 0) (1, 0)).card = 3 := by decide

example : lineColorPeriod 3 8 (0, 1) = 8 := by decide

example : lineColorPeriod 2 8 (0, 1) = 4 := by decide
