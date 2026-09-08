import CLRSLean.FourthEdition.Chapter_27.Section_27_1_Waiting_For_Elevator
import CLRSLean.Audit.Axioms
open CLRS.SkiRental
example (s : Strategy) : ∃ T : Nat, 0 < T ∧ 0 < optCost 1 10 T ∧
    (2 - 1 / 10 : ℝ) * optCost 1 10 T ≤ onlineCost 1 10 s T :=
  skiRental_lower_bound 1 10 (by norm_num) (by norm_num) s
example (s : Strategy) : ∃ T : Nat, 0 < T ∧
    (3/2 : ℝ) * optCost 1 10 T < onlineCost 1 10 s T :=
  skiRental_not_competitive_below 1 10 (3/2) (by norm_num) (by norm_num) s (by norm_num)
#assert_axioms skiRental_lower_bound
#assert_axioms skiRental_not_competitive_below
