import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check FFTMultiplicationExecution
#check FFTMultiplicationExecution.work
#check scaleVectorExec
#check scaleVectorExec_work_exact
#check fftMultiplyExecAt
#check fftMultiplyAt
#check fftMultiplyExecAt_value
#check fftMultiplyAt_correct
#check polySize
#check multiplicationInputSize
#check complexFFTExponent
#check complexFFTCapacity
#check complexFFTRoot
#check complexFFTMultiply
#check complexFFTMultiply_correct
#check radix2FFTMultiplyWork
#check fftMultiplyExecAt_work_exact
#check fftMultiplyExecution
#check fftMultiplyExecution_work_eq
#check fftMultiplyExecution_correct
#check fftMultiplyWork
#check fftMultiplyWork_allInput_bigTheta

open Polynomial

example :
    fftMultiplyAt (k := 1) (-1 : ℚ) (Polynomial.C 2)
      (Polynomial.X + Polynomial.C 3) =
        Polynomial.C 2 * (Polynomial.X + Polynomial.C 3) := by
  apply fftMultiplyAt_correct (IsPrimitiveRoot.neg_one 0 (by norm_num))
  norm_num [Polynomial.degree_mul]

example :
    fftMultiplyAt (k := 2)
      (Complex.exp (2 * Real.pi * Complex.I / 4))
      (1 + Polynomial.X) (1 - Polynomial.X) =
        (1 + Polynomial.X) * (1 - Polynomial.X) := by
  apply fftMultiplyAt_correct_of_degree_lt (m := 2) (n := 2)
    (Complex.isPrimitiveRoot_exp 4 (by norm_num))
  · rw [show (1 + Polynomial.X : ℂ[X]) =
        Polynomial.X + Polynomial.C 1 by simp [add_comm]]
    rw [Polynomial.degree_X_add_C]
    norm_num
  · rw [show (1 - Polynomial.X : ℂ[X]) =
        -(Polynomial.X - Polynomial.C 1) by simp]
    rw [Polynomial.degree_neg, Polynomial.degree_X_sub_C]
    norm_num
  · norm_num

example :
    fftMultiplyAt (k := 2)
      (Complex.exp (2 * Real.pi * Complex.I / 4))
      (Polynomial.X ^ 2) Polynomial.X = Polynomial.X ^ 3 := by
  have h := fftMultiplyAt_correct (k := 2)
    (Complex.isPrimitiveRoot_exp 4 (by norm_num))
    (Polynomial.X ^ 2 : ℂ[X]) Polynomial.X (by norm_num)
  simpa [pow_succ] using h

example : complexFFTMultiply (0 : ℂ[X]) 0 = 0 := by
  rw [complexFFTMultiply_correct]
  simp

example : complexFFTMultiply (0 : ℂ[X]) (Polynomial.X + 1) = 0 := by
  rw [complexFFTMultiply_correct]
  simp

example :
    complexFFTMultiply (Polynomial.C (2 : ℂ)) (Polynomial.C 3) =
      Polynomial.C 6 := by
  rw [complexFFTMultiply_correct]
  rw [← Polynomial.C_mul]
  norm_num

example :
    complexFFTMultiply
      (Polynomial.X + 0 * Polynomial.X ^ 4 : ℂ[X])
      (Polynomial.X + 1) = Polynomial.X * (Polynomial.X + 1) := by
  rw [complexFFTMultiply_correct]
  simp

example :
    complexFFTMultiply (1 + Polynomial.X : ℂ[X])
      (1 - Polynomial.X) = 1 - Polynomial.X ^ 2 := by
  rw [complexFFTMultiply_correct]
  ring

example :
    radix2FFTMultiplyWork 0 = 2 ∧
    radix2FFTMultiplyWork 1 = 16 ∧
    radix2FFTMultiplyWork 2 = 56 := by
  native_decide

example :
    (fftMultiplyExecAt (k := 1) (-1 : ℚ) (Polynomial.C 2)
      (Polynomial.X + Polynomial.C 3)).value =
        Polynomial.C 2 * (Polynomial.X + Polynomial.C 3) ∧
    (fftMultiplyExecAt (k := 1) (-1 : ℚ) (Polynomial.C 2)
      (Polynomial.X + Polynomial.C 3)).work = 16 := by
  constructor
  · rw [fftMultiplyExecAt_value]
    apply fftMultiplyAt_correct (IsPrimitiveRoot.neg_one 0 (by norm_num))
    norm_num [Polynomial.degree_mul]
  · rw [fftMultiplyExecAt_work_exact]
    norm_num [radix2FFTMultiplyWork, radix2FFTWork]

end CLRS.Chapter30
