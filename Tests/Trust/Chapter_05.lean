import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_05

/-! # Chapter 5 flagship trust surface -/

#check CLRS.Chapter05.randomizeInPlace_uniform
#check CLRS.Chapter05.expectedLongestStreak_lowerBound
#check CLRS.Chapter05.OnlineHiring.probHireBest_asymptotic

#assert_axioms CLRS.Chapter05.randomizeInPlace_uniform
#assert_axioms CLRS.Chapter05.expectedLongestStreak_lowerBound
#assert_axioms CLRS.Chapter05.OnlineHiring.probHireBest_asymptotic

example : CLRS.Chapter05.hireAssistant [3, 1, 4, 1, 5, 9, 2, 6] = 4 := by
  decide
