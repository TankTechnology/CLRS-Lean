import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_30

/-! # Chapter 30 flagship trust surface -/

#check CLRS.Chapter30.recursiveFFT_eq_dft
#check CLRS.Chapter30.complexFFTMultiply_correct
#check CLRS.Chapter30.iterativeRadix2FFTTotalWork_bigTheta

#assert_axioms CLRS.Chapter30.recursiveFFT_eq_dft
#assert_axioms CLRS.Chapter30.complexFFTMultiply_correct
#assert_axioms CLRS.Chapter30.iterativeRadix2FFTTotalWork_bigTheta

example : CLRS.Chapter30.dft (-1 : ℚ) ![(3 : ℚ), 5] = ![(8 : ℚ), -2] := by
  funext k
  fin_cases k <;> norm_num [CLRS.Chapter30.dft, CLRS.Chapter30.powerPoints,
    Fin.sum_univ_succ]
