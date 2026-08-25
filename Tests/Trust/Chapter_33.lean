import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_33

/-! # Chapter 33 flagship trust surface -/

#check CLRS.KMeans.lloyd_iteration_cost_le
#check CLRS.MultiplicativeWeights.totalExpectedLoss_le
#check CLRS.GradientDescent.avgIterate_suboptimality_le

#assert_axioms CLRS.KMeans.lloyd_iteration_cost_le
#assert_axioms CLRS.MultiplicativeWeights.totalExpectedLoss_le
#assert_axioms CLRS.GradientDescent.avgIterate_suboptimality_le
