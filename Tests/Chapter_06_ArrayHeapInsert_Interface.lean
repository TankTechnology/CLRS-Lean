import CLRSLean.FourthEdition.Chapter_06

#check CLRS.Chapter06.arrayHeapInsert?
#check CLRS.Chapter06.arrayHeapInsert?_eq_none_iff
#check CLRS.Chapter06.arrayHeapInsert?_state_correct
#check CLRS.Chapter06.arrayHeapIncreaseKeyBubbleUpFuelWithCost
#check CLRS.Chapter06.arrayHeapIncreaseKeyBubbleUpFuelWithCost_result
#check CLRS.Chapter06.arrayHeapIncreaseKeyBubbleUpFuelWithCost_cost_le_log
#check CLRS.Chapter06.arrayHeapInsertWithCost?
#check CLRS.Chapter06.arrayHeapInsertWithCost?_result
#check CLRS.Chapter06.arrayHeapInsertWithCost?_state_correct_and_log_cost

example : CLRS.Chapter06.arrayHeapInsert? [9, 4, 7, 99] 3 8 =
    some ([9, 8, 7, 4, 99], 4) := by
  decide

example : CLRS.Chapter06.arrayHeapInsert? [9, 4, 7] 4 8 = none := by
  decide
