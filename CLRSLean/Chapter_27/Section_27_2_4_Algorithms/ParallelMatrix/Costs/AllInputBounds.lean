import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs.PowerBounds

/-!
# CLRS Section 27.2 — All-Input Matrix Asymptotics

This module lifts the exact-power analysis of executable {lit}`P-ADD` and
{lit}`P-MATMUL` to every natural input size.  The results distinguish the
execution-attached P-MATMUL span, which includes its sequential P-ADD stage and
therefore grows as {lit}`Theta(log^2 n)`, from the earlier idealized recurrence.

Main results:

- Theorem {lit}`pAddWork_allInput_bigTheta`: P-ADD work is quadratic.
- Theorem {lit}`pAddSpan_allInput_bigTheta`: P-ADD span is logarithmic.
- Theorem {lit}`pMatMulExecWork_allInput_bigTheta`: executable P-MATMUL work is
  cubic.
- Theorem {lit}`pMatMulExecSpan_allInput_bigTheta`: executable P-MATMUL span is
  log-squared ({lit}`Theta(log^2 n)`).
-/

namespace CLRS
namespace Chapter27

/-- P-ADD has quadratic work on every positive input size. -/
theorem pAddWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pAddWork n : ℝ))
      (Chapter04.polynomialScale 2) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pAddWork n : ℝ))
        (Chapter04.criticalPowerScale 4 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 4 2
      (fun n : ℕ => (pAddWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast pAddWork_monotone)
      pAddWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerScale_isBigTheta_polynomialScale 2 2
      (by norm_num))

/-- P-ADD has logarithmic span on every positive input size. -/
theorem pAddSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pAddSpan n : ℝ))
      (Chapter04.polynomialLogScale 2 0) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pAddSpan n : ℝ))
        (Chapter04.criticalPowerLogScale 1 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerLogScale 1 2
      (fun n : ℕ => (pAddSpan n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast pAddSpan_monotone) (by
        simpa only [Nat.cast_one, one_pow, mul_one] using
          pAddSpan_exactPower_bigTheta)
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerLogScale_isBigTheta_polynomialLogScale
      2 0 (by norm_num))

/-- Executable P-MATMUL has cubic work on every positive input size. -/
theorem pMatMulExecWork_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMatMulExecWork n : ℝ))
      (Chapter04.polynomialScale 3) := by
  have hcritical :
      Chapter03.isBigTheta (fun n : ℕ => (pMatMulExecWork n : ℝ))
        (Chapter04.criticalPowerScale 8 2) :=
    Chapter04.allInput_bigTheta_of_criticalPowerScale 8 2
      (fun n : ℕ => (pMatMulExecWork n : ℝ)) (by norm_num) (by norm_num)
      (Chapter04.monotoneAbs_natCast pMatMulExecWork_monotone)
      pMatMulExecWork_exactPower_bigTheta
  exact Chapter03.isBigTheta_trans hcritical (by
    simpa using Chapter04.criticalPowerScale_isBigTheta_polynomialScale 2 3
      (by norm_num))

/-- Executable P-MATMUL has log-squared span, {lit}`Theta(log^2 n)`, on every
positive input size.  This is the actual span of the costed implementation,
including the sequential P-ADD phase. -/
theorem pMatMulExecSpan_allInput_bigTheta :
    Chapter03.isBigTheta (fun n : ℕ => (pMatMulExecSpan n : ℝ))
      (Chapter04.criticalPowerLogPolylogScale 1 2 1) := by
  have hpower :
      Chapter03.isBigTheta
        (fun i : ℕ => (pMatMulExecSpan (2 ^ i) : ℝ))
        (fun i : ℕ =>
          Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) := by
    have hscale :
        (fun i : ℕ =>
          Chapter04.criticalPowerLogPolylogScale 1 2 1 (2 ^ i)) =
          (fun i : ℕ => ((i : ℝ) + 1) ^ 2) := by
      funext i
      simp [Chapter04.criticalPowerLogPolylogScale_exactPower]
    rw [hscale]
    exact pMatMulExecSpan_exactPower_bigTheta
  exact Chapter04.allInput_bigTheta_of_powerStep 2
    (fun n : ℕ => (pMatMulExecSpan n : ℝ))
    (Chapter04.criticalPowerLogPolylogScale 1 2 1) (by norm_num)
    (Chapter04.monotoneAbs_natCast pMatMulExecSpan_monotone)
    (Chapter04.criticalPowerLogPolylogScale_monotoneAbs 1 2 1 (by norm_num))
    (Chapter04.criticalPowerLogPolylogScale_powerStepBound 1 2 1
      (by norm_num) (by norm_num))
    hpower

end Chapter27
end CLRS
