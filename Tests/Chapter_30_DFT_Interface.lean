import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check primitiveRoot_powers_injective
#check primitiveRoot_square
#check primitiveRoot_half_pow_eq_neg_one
#check primitiveRoot_inv
#check root_sum_orthogonality
#check powerPoints
#check dft
#check dft_eq_pointValues
#check complexDft_mathlib
#check idft
#check idft_dft
#check dft_idft
#check dft_injective
#check cyclicSub
#check cyclicConvolution
#check dft_cyclicConvolution
#check idft_pointwiseMul
#check cyclicConvolution_eq_coeffVector_mul

example : dft (1 : ℚ) ![(7 : ℚ)] = ![(7 : ℚ)] := by
  native_decide

example : dft (-1 : ℚ) ![(3 : ℚ), 5] = ![(8 : ℚ), -2] := by
  native_decide

example :
    dft Complex.I ![(1 : ℂ), 0, 0, 0] = ![(1 : ℂ), 1, 1, 1] := by
  funext k
  fin_cases k <;> simp [dft, Fin.sum_univ_succ]

example (a : CoeffVector ℂ 1) :
    idft (Complex.exp (2 * Real.pi * Complex.I / 1))
      (dft (Complex.exp (2 * Real.pi * Complex.I / 1)) a) = a := by
  simpa using
    (idft_dft (by norm_num) (Complex.isPrimitiveRoot_exp 1 (by norm_num)) a)

example (a : CoeffVector ℂ 1) :
    dft (Complex.exp (2 * Real.pi * Complex.I / 1))
      (idft (Complex.exp (2 * Real.pi * Complex.I / 1)) a) = a := by
  simpa using
    (dft_idft (by norm_num) (Complex.isPrimitiveRoot_exp 1 (by norm_num)) a)

example (a : CoeffVector ℚ 2) :
    idft (-1 : ℚ) (dft (-1 : ℚ) a) = a :=
  idft_dft (by norm_num) (IsPrimitiveRoot.neg_one 0 (by norm_num)) a

example (a : CoeffVector ℚ 2) :
    dft (-1 : ℚ) (idft (-1 : ℚ) a) = a :=
  dft_idft (by norm_num) (IsPrimitiveRoot.neg_one 0 (by norm_num)) a

example :
    idft (Complex.exp (2 * Real.pi * Complex.I / 4))
      (dft (Complex.exp (2 * Real.pi * Complex.I / 4))
        ![(1 : ℂ), 0, 3, 0]) = ![(1 : ℂ), 0, 3, 0] := by
  simpa using
    (idft_dft (by norm_num) (Complex.isPrimitiveRoot_exp 4 (by norm_num))
      ![(1 : ℂ), 0, 3, 0])

example :
    dft (Complex.exp (2 * Real.pi * Complex.I / 4))
      (idft (Complex.exp (2 * Real.pi * Complex.I / 4))
        ![(1 : ℂ), 0, 3, 0]) = ![(1 : ℂ), 0, 3, 0] := by
  simpa using
    (dft_idft (by norm_num) (Complex.isPrimitiveRoot_exp 4 (by norm_num))
      ![(1 : ℂ), 0, 3, 0])

example :
    cyclicConvolution (K := ℚ) (n := 4) (by norm_num)
      ![(1 : ℚ), 1, 0, 0] ![(1 : ℚ), 1, 0, 0] =
      ![(1 : ℚ), 2, 1, 0] := by
  native_decide

end CLRS.Chapter30
