import CLRSLean.FourthEdition.Chapter_02

#check CLRS.Chapter02.InsertionSortLineCosts
#check CLRS.Chapter02.InsertionSortLineCounts
#check CLRS.Chapter02.insertionSortLineCounts
#check CLRS.Chapter02.insertionSortRunningTime
#check CLRS.Chapter02.insertionSortRunningTime_eq_textbook_sum
#check CLRS.Chapter02.insertionSortLineCounts_best_case
#check CLRS.Chapter02.insertionSortLineCounts_worst_case
#check CLRS.Chapter02.insertionSortRunningTime_best_case
#check CLRS.Chapter02.insertionSortRunningTime_worst_case

example :
    CLRS.Chapter02.insertionSortLineCounts 5 (fun _ => 1) =
      { forLoopTests := 5
        keyAssignments := 4
        indexInitializations := 4
        whileLoopTests := 4
        shifts := 0
        decrements := 0
        finalAssignments := 4 } := by
  decide
