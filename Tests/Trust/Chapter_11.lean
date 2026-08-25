import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_11

/-! # Chapter 11 flagship trust surface -/

#check CLRS.Chapter11.affineHashMod_isUniversal
#check CLRS.Chapter11.expectedSuccessfulProbes_le_ln
#check CLRS.Chapter11.perfectHash_expected_total_space_lt_2n

#assert_axioms CLRS.Chapter11.affineHashMod_isUniversal
#assert_axioms CLRS.Chapter11.expectedSuccessfulProbes_le_ln
#assert_axioms CLRS.Chapter11.perfectHash_expected_total_space_lt_2n

example : CLRS.Chapter11.divisionHash 10 42 = 2 := by
  decide
