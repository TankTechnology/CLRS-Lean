import CLRSLean.Chapter_30

namespace CLRS.Chapter30

#check CoeffVector
#check PowTwoVec
#check coeffVector
#check vectorToPolynomial
#check vectorToPolynomial_coeff
#check coeffVector_vectorToPolynomial
#check vectorToPolynomial_coeffVector
#check hornerEvalExec
#check hornerEval
#check hornerEval_correct
#check hornerEvalWork_exact
#check pointValues
#check interpolateVector
#check pointValues_injective
#check interpolate_pointValues
#check interpolate_unique
#check interpolate_pointValues_roundTrip
#check pointValues_add
#check pointValues_mul
#check VectorArithmeticExecution
#check vectorAddExec
#check vectorAddWork_exact
#check pointwiseMulExec
#check pointwiseMulWork_exact
#check schoolbookMulExec
#check schoolbookMul
#check schoolbookMul_correct
#check schoolbookMul_degreeBound
#check schoolbookMulWork_exact

open Polynomial

example : interpolateVector (fun i : Fin 0 => (Fin.elim0 i : ℚ))
    (fun i : Fin 0 => (Fin.elim0 i : ℚ)) = 0 := by
  simp [interpolateVector]

example : interpolateVector (fun _ : Fin 1 => (2 : ℚ))
    (pointValues (fun _ : Fin 1 => (2 : ℚ)) (Polynomial.C 7)) =
      Polynomial.C 7 := by
  apply interpolate_pointValues_roundTrip
  · intro i j _
    exact Subsingleton.elim i j
  · norm_num

example : interpolateVector (fun i : Fin 2 => (i.1 : ℚ))
    (pointValues (fun i : Fin 2 => (i.1 : ℚ)) (Polynomial.X + 1)) =
      Polynomial.X + 1 := by
  apply interpolate_pointValues_roundTrip
  · intro i j hij
    apply Fin.ext
    exact Nat.cast_inj.mp hij
  · rw [show (1 : ℚ[X]) = Polynomial.C 1 by simp,
      Polynomial.degree_X_add_C]
    norm_num

example : schoolbookMul (fun i : Fin 0 => (Fin.elim0 i : Nat))
    ![1, 2] = ![0, 0] := by
  native_decide

example : schoolbookMul ![(2 : Nat)] ![3] = ![6, 0] := by
  native_decide

example : schoolbookMul ![(1 : Nat), 0, 2] ![0, 3] =
    ![0, 3, 0, 6, 0] := by
  native_decide

example : schoolbookMul ![(1 : Nat), 1] ![1, 1] = ![1, 2, 1, 0] := by
  native_decide

end CLRS.Chapter30
