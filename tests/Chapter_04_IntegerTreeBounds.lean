import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Asymptotics
open CLRS.Chapter04
#check balancedIntegerCost_isBigTheta
#check unbalancedIntegerCost_isBigTheta
#check balancedIntegerCost_bounds
#check unbalancedIntegerCost_bounds

-- Both claims concern the actual generated trees, with no supplied Θ premise.
example (c base : ℝ) (hc : 0 < c) (hb : 0 ≤ base) :
    CLRS.Chapter03.isBigTheta (balancedIntegerCost c base)
      (fun n : ℕ => (n : ℝ)^2) := balancedIntegerCost_isBigTheta hc hb

example (c base : ℝ) (hc : 0 < c) (hb : 0 ≤ base) :
    CLRS.Chapter03.isBigTheta (unbalancedIntegerCost c base)
      (fun n : ℕ => (n : ℝ)*Real.log (n : ℝ)) := unbalancedIntegerCost_isBigTheta hc hb

-- Zero-cost leaves are allowed: positive internal charges provide the lower bound.
example : CLRS.Chapter03.isBigTheta (unbalancedIntegerCost 1 0)
    (fun n : ℕ => (n : ℝ)*Real.log (n : ℝ)) :=
  unbalancedIntegerCost_isBigTheta (by norm_num) (by norm_num)

-- The balanced expansion includes its three zero-size children at input two.
example : balancedIntegerCost 1 1 2 = 7 := by
  rw [balancedIntegerCost_step (by norm_num : 1 < 2)]
  norm_num [balancedIntegerCost_base]

-- Unequal branches at input four: the size-one child stops, size three expands.
example : unbalancedIntegerCost 1 1 4 = 10 := by
  have hthree : unbalancedIntegerCost 1 1 3 = 5 := by
    rw [unbalancedIntegerCost_step (by norm_num : 2 < 3)]
    norm_num [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div, unbalancedIntegerCost_base]
  rw [unbalancedIntegerCost_step (by norm_num : 2 < 4)]
  norm_num [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div, unbalancedIntegerCost_base, hthree]

-- The upper potential explicitly covers the zero-size base case.
example (c base : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ base) :
    balancedIntegerCost c base 0 ≤ 4*c+base := by
  simpa using (balancedIntegerCost_bounds hc hb 0).2
