import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_15

/-! # Chapter 15 flagship trust surface -/

#check CLRS.ActivitySelection.activitySelection_correct
#check CLRS.HuffmanV2.huffmanOfFreqs_correct
#check CLRS.Caching.fifo_optimal

#assert_axioms CLRS.ActivitySelection.activitySelection_correct
#assert_axioms CLRS.HuffmanV2.huffmanOfFreqs_correct
#assert_axioms CLRS.Caching.fifo_optimal

example :
    CLRS.ActivitySelection.activitySelection
      [{ start := 0, finish := 2 }, { start := 1, finish := 4 },
        { start := 3, finish := 5 }] =
      [{ start := 0, finish := 2 }, { start := 3, finish := 5 }] := by
  norm_num [CLRS.ActivitySelection.activitySelection, CLRS.ActivitySelection.greedySelect,
    CLRS.ActivitySelection.activitiesAfter, CLRS.ActivitySelection.Before]
