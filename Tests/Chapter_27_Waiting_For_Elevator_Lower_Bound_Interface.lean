import CLRSLean.FourthEdition.Chapter_27

/-!
# Chapter 27 §27.1 deterministic lower bound interface test

Verifies the ski-rental and elevator deterministic lower bounds: the general
causal strategy model, the `2 - r/p` lower bound, and the `2 - E/S` elevator
corollary.
-/

namespace CLRS

-- §27.1 ski rental: causal strategy model and the deterministic lower bound.
#check SkiRental.Strategy
#check SkiRental.onlineCost
#check SkiRental.rentThenBuy_lower_bound
#check SkiRental.skiRental_lower_bound
#check SkiRental.rentThenBuy_two_competitive

#print axioms SkiRental.rentThenBuy_lower_bound
#print axioms SkiRental.skiRental_lower_bound

-- §27.1 elevator: the deterministic lower-bound corollary.
#check Elevator.elevator_lower_bound
#check Elevator.elevator_two_competitive
#check Elevator.elevator_worst_case_ratio

#print axioms Elevator.elevator_lower_bound

end CLRS
