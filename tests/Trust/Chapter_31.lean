import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_31

/-! # Chapter 31 flagship trust surface -/

#check CLRS.Chapter31.modularLinearEquationSolver_complete
#check CLRS.Chapter31.rsaKeyGen_spec
#check CLRS.Chapter31.strongLiars_nat_card_le

#assert_axioms CLRS.Chapter31.modularLinearEquationSolver_complete
#assert_axioms CLRS.Chapter31.rsaKeyGen_spec
#assert_axioms CLRS.Chapter31.strongLiars_nat_card_le

example : Nat.gcd 4 6 * Nat.lcm 4 6 = 4 * 6 :=
  CLRS.Chapter31.gcd_mul_lcm_eq 4 6

#check CLRS.Chapter31.euclidWithCount_spec
#check CLRS.Chapter31.rsaKeyGen_roundTrip
#check CLRS.Chapter31.MillerRabinExecution.run_spec
#check CLRS.Chapter31.MillerRabinExecution.uniform_error_le
#assert_axioms CLRS.Chapter31.euclidWithCount_spec
#assert_axioms CLRS.Chapter31.rsaKeyGen_roundTrip_mod
#assert_axioms CLRS.Chapter31.rsaKeyGen_roundTrip
#assert_axioms CLRS.Chapter31.MillerRabinExecution.trial_spec
#assert_axioms CLRS.Chapter31.MillerRabinExecution.run_spec
#assert_axioms CLRS.Chapter31.MillerRabinExecution.run_count_le
#assert_axioms CLRS.Chapter31.MillerRabinExecution.accepted_card
#assert_axioms CLRS.Chapter31.MillerRabinExecution.uniform_error_le
