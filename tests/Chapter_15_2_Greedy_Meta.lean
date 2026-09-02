import CLRSLean.FourthEdition.Chapter_15.Section_15_2_Greedy_Meta.ActivitySelection

open CLRS

#check GreedyMeta.GreedyChoiceProperty
#check GreedyMeta.OptimalSubstructure
#check GreedyMeta.activityGreedyChoiceProperty
#check GreedyMeta.activityOptimalSubstructure
#check GreedyMeta.activityGsolve_maxCardinality
#check GreedyMeta.activityGsolve_eq_greedySelect
#check GreedyMeta.greedySelect_maxCardinality_via_meta

example :
    GreedyMeta.activitySize
      (⟨[{ start := 0, finish := 2 }, { start := 3, finish := 5 }], by
        simp [ActivitySelection.FinishSorted]⟩ : GreedyMeta.SortedActivityProblem) = 2 := by
  decide
