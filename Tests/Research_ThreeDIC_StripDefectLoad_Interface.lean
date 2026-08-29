import CLRSLean.Research.ThreeDIC.StripDefectLoad

open CLRS.Research.ThreeDIC

#check stripPoint
#check stripLinePoints
#check stripPoints
#check stripColorPoints
#check stripAcrossColorPeriod
#check stripAcrossColorPeriod_pos
#check stripColor_load_le_sum_lines
#check stripColor_load_le_phase_periods
#check stripColor_horizontal_load_le
#check stripColor_vertical_load_le_phase
#check stripColor_finiteGrid_load_le_phase_periods

example :
    (stripColorPoints 3 8 2 5 3 (0, 0) (1, 0) (0, 1)).card = 2 := by
  decide

example :
    (stripColorPoints 2 8 4 5 0 (0, 0) (0, 1) (1, 0)).card = 3 := by
  decide

example :
    (stripColorPoints 3 8 0 5 0 (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (stripColorPoints 3 8 3 4 0 (0, 0) (0, 0) (0, 0)).card = 1 := by
  decide
