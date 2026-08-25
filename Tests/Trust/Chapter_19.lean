import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_19

/-! # Chapter 19 flagship trust surface -/

#check CLRS.Chapter21.Forest.union_refines_merge
#check CLRS.Chapter21.Analysis.Costed.run_refines_spec
#check CLRS.Chapter21.Analysis.Ackermann.run_cost_le_inverseAckermann_of_universe_le_ops

#assert_axioms CLRS.Chapter21.Forest.union_refines_merge
#assert_axioms CLRS.Chapter21.Analysis.Costed.run_refines_spec
#assert_axioms CLRS.Chapter21.Analysis.Ackermann.run_cost_le_inverseAckermann_of_universe_le_ops

example :
    (CLRS.Chapter21.Partition.discrete : CLRS.Chapter21.Partition Nat).sameSet 2 2 := by
  rfl
