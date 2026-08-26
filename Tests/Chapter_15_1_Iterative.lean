import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection.Iterative

open CLRS.ActivitySelection

#check TextbookActivity
#check greedySelectIterative_eq_greedySelect
#check greedySelectIterative_maxCardinality
#check greedySelectIterativeCost_steps

example :
    greedySelectIterative
      [{ start := 0, finish := 2 }, { start := 1, finish := 4 },
        { start := 3, finish := 5 }] =
      [{ start := 0, finish := 2 }, { start := 3, finish := 5 }] := by
  decide

example :
    (greedySelectIterativeCost
      [{ start := 0, finish := 2 }, { start := 1, finish := 4 },
        { start := 3, finish := 5 }]).2 = 3 := by
  decide

