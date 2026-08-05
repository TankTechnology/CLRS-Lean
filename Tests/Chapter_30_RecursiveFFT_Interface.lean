import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check evenIndex
#check oddIndex
#check evenCoeffs
#check oddCoeffs
#check twiddlePowersAux
#check TwiddleExecution
#check twiddlePowersAuxExec
#check twiddlePowers
#check twiddlePowers_eq_pow
#check twiddleChildRoot
#check twiddleChildRoot_eq_square
#check butterflyLayer
#check ButterflyExecution
#check butterflyLayerExec
#check FFTExecution
#check FFTExecution.work
#check recursiveFFTExec
#check recursiveFFT
#check recursiveFFTExec_value
#check polynomial_evenOdd_split
#check recursiveFFT_eq_dft
#check recursiveIFFT
#check recursiveIFFT_eq_idft
#check recursiveIFFT_recursiveFFT
#check recursiveFFT_recursiveIFFT
#check recursiveFFTWork
#check recursiveFFTWork_exact
#check fftExponent
#check fftCapacity
#check paddedFFTWork
#check fftCapacity_ge
#check fftCapacity_lt_two_mul
#check paddedFFTWork_allInput_bigTheta

example : twiddlePowers (2 : ℚ) 4 = ![(1 : ℚ), 2, 4, 8] := by
  funext i
  fin_cases i <;> norm_num [twiddlePowers_eq_pow]

example :
    (recursiveFFTExec (k := 1) (-1 : ℚ)
      (![(3 : ℚ), 5] : PowTwoVec ℚ 1)).value =
        (![(8 : ℚ), -2] : PowTwoVec ℚ 1) ∧
    (recursiveFFTExec (k := 1) (-1 : ℚ)
      (![(3 : ℚ), 5] : PowTwoVec ℚ 1)).addSubtractions = 2 ∧
    (recursiveFFTExec (k := 1) (-1 : ℚ)
      (![(3 : ℚ), 5] : PowTwoVec ℚ 1)).multiplications = 2 := by
  native_decide

example :
    recursiveFFTWork (k := 2) (1 : ℚ)
      (![(1 : ℚ), 2, 3, 4] : PowTwoVec ℚ 2) = 16 := by
  native_decide

example : fftCapacity 3 = 4 ∧ paddedFFTWork 4 = 16 := by
  native_decide

example :
    recursiveFFT (k := 2) (Complex.exp (2 * Real.pi * Complex.I / 4))
        (![(1 : ℂ), 0, 3, 0] : PowTwoVec ℂ 2) =
      dft (Complex.exp (2 * Real.pi * Complex.I / 4))
        (![(1 : ℂ), 0, 3, 0] : PowTwoVec ℂ 2) :=
  recursiveFFT_eq_dft (Complex.isPrimitiveRoot_exp 4 (by norm_num)) _

example (a : PowTwoVec ℂ 0) :
    recursiveIFFT (k := 0) (Complex.exp (2 * Real.pi * Complex.I / 1))
      (recursiveFFT (k := 0)
        (Complex.exp (2 * Real.pi * Complex.I / 1)) a) = a :=
  by
    simpa using recursiveIFFT_recursiveFFT
      (Complex.isPrimitiveRoot_exp 1 (by norm_num)) a

example (a : PowTwoVec ℚ 1) :
    recursiveFFT (k := 1) (-1 : ℚ)
      (recursiveIFFT (k := 1) (-1 : ℚ) a) = a :=
  recursiveFFT_recursiveIFFT (IsPrimitiveRoot.neg_one 0 (by norm_num)) a

example :
    recursiveIFFT (k := 2) (Complex.exp (2 * Real.pi * Complex.I / 4))
      (recursiveFFT (k := 2) (Complex.exp (2 * Real.pi * Complex.I / 4))
        (![(1 : ℂ), 0, 3, 0] : PowTwoVec ℂ 2)) =
      (![(1 : ℂ), 0, 3, 0] : PowTwoVec ℂ 2) :=
  recursiveIFFT_recursiveFFT
    (Complex.isPrimitiveRoot_exp 4 (by norm_num)) _

#print axioms recursiveFFTExec_value
#print axioms recursiveFFT_eq_dft
#print axioms recursiveIFFT_eq_idft
#print axioms recursiveFFTWork_exact
#print axioms paddedFFTWork_allInput_bigTheta

end CLRS.Chapter30
