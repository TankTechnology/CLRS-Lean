import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_27

/-! # Chapter 27 flagship trust surface -/

#check CLRS.SkiRental.rentThenBuy_two_competitive
#check CLRS.SearchList.mtf_four_competitive
#check CLRS.OnlineCaching.lru_k_competitive

#assert_axioms CLRS.SkiRental.rentThenBuy_two_competitive
#assert_axioms CLRS.SearchList.mtf_four_competitive
#assert_axioms CLRS.OnlineCaching.lru_k_competitive

example : CLRS.OnlineCaching.lruMisses 2 [] [0, 1, 0, 2] = 3 := by
  decide

#assert_axioms CLRS.OnlineCaching.algorithm_nonempty
#assert_axioms CLRS.OnlineCaching.Policy.no_real_competitive
#assert_axioms CLRS.OnlineCaching.Schedule.lru_k_competitive
#assert_axioms CLRS.OnlineCaching.offline_schedule_valid
#assert_axioms CLRS.SkiRental.skiRental_not_competitive_below
