import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_15

/-! # Chapter 15 flagship trust surface -/

#check CLRS.ActivitySelection.activitySelection_correct
#check CLRS.ActivitySelection.greedySelectIterative_eq_greedySelect
#check CLRS.ActivitySelection.greedySelectIterativeCost_steps
#check CLRS.GreedyMeta.activityGsolve_eq_greedySelect
#check CLRS.HuffmanV2.huffmanOfFreqs_correct
#check CLRS.HuffmanV2.textbookCost_eq_cost
#check CLRS.HuffmanV2.lemma15_2_greedy_choice
#check CLRS.HuffmanV2.lemma15_3_optimal_substructure
#check CLRS.HuffmanV2.huffmanOfFreqsComparisons_le_quadratic
#check CLRS.Caching.fifo_optimal
#check CLRS.Caching.fifo_optimal_from_empty
#check CLRS.Caching.fifo_optimal_after_compulsory_fill

#assert_axioms CLRS.ActivitySelection.activitySelection_correct
#assert_axioms CLRS.ActivitySelection.greedySelectIterative_eq_greedySelect
#assert_axioms CLRS.ActivitySelection.greedySelectIterativeCost_steps
#assert_axioms CLRS.GreedyMeta.activityGsolve_eq_greedySelect
#assert_axioms CLRS.HuffmanV2.huffmanOfFreqs_correct
#assert_axioms CLRS.HuffmanV2.textbookCost_eq_cost
#assert_axioms CLRS.HuffmanV2.lemma15_2_greedy_choice
#assert_axioms CLRS.HuffmanV2.lemma15_3_optimal_substructure
#assert_axioms CLRS.HuffmanV2.huffmanOfFreqsComparisons_le_quadratic
#assert_axioms CLRS.Caching.fifo_optimal
#assert_axioms CLRS.Caching.fifo_optimal_from_empty
#assert_axioms CLRS.Caching.fifo_optimal_after_compulsory_fill

example :
    CLRS.ActivitySelection.activitySelection
      [{ start := 0, finish := 2 }, { start := 1, finish := 4 },
        { start := 3, finish := 5 }] =
      [{ start := 0, finish := 2 }, { start := 3, finish := 5 }] := by
  norm_num [CLRS.ActivitySelection.activitySelection, CLRS.ActivitySelection.greedySelect,
    CLRS.ActivitySelection.activitiesAfter, CLRS.ActivitySelection.Before]
