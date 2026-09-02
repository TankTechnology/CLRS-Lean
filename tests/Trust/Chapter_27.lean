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
