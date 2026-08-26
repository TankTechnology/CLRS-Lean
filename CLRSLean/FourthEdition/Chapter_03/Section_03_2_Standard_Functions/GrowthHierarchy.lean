import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions.GrowthBridges
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

open Filter
open Asymptotics
open scoped Topology

/-!
# The complete CLRS growth hierarchy

This file supplies the two comparison layers that are easy to omit from a
short growth table: arbitrary real powers, and the superpolynomial but
subexponential function `n^(log n)`.  The latter is represented by the
extension-safe real expression `exp ((log n)^2)`; the two expressions agree
for every positive `n`.
-/

namespace CLRS
namespace Chapter03

/-- An everywhere-defined real representation of `n^(log n)`. -/
noncomputable def nPowLog (n : ℕ) : ℝ :=
  Real.exp (Real.log (n : ℝ) ^ 2)

/-- On positive inputs, `nPowLog n` is exactly the real power `n^(log n)`. -/
theorem nPowLog_eq_rpow_log {n : ℕ} (hn : 0 < n) :
    nPowLog n = (n : ℝ) ^ Real.log (n : ℝ) := by
  rw [nPowLog, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

/-- Strictly larger real powers dominate smaller ones. -/
theorem isLittleO_rpow_rpow {a b : ℝ} (hab : a < b) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a)
      (fun n : ℕ => (n : ℝ) ^ b) := by
  unfold isLittleO
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop 0] with n hn _hzero
    exact False.elim ((Real.rpow_pos_of_pos
      (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn) b).ne' _hzero)
  · have hlim : Tendsto (fun x : ℝ => x ^ (-(b - a))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    have hcomp := hlim.comp tendsto_natCast_atTop_atTop
    apply hcomp.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply]
    rw [show -(b - a) = a - b by ring,
      Real.rpow_sub (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)]

/-- Every fixed real power is dominated by `n^(log n)`. -/
theorem isLittleO_rpow_nPowLog (a : ℝ) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) nPowLog := by
  unfold isLittleO
  apply isLittleO_of_tendsto'
  · exact Eventually.of_forall fun n hzero =>
      (Real.exp_ne_zero (Real.log (n : ℝ) ^ 2) hzero).elim
  · have hgauss :
        Tendsto (fun x : ℝ => Real.exp ((-1) * x ^ 2 + a * x)) atTop (𝓝 0) := by
      have ho := rexp_neg_quadratic_isLittleO_rpow_atTop
        (a := (-1 : ℝ)) (by norm_num) a 0
      simpa using ho.tendsto_div_nhds_zero
    have hcomp := hgauss.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    apply hcomp.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n), nPowLog,
      ← Real.exp_sub]
    congr 1
    ring

/-- The `n^(log n)` layer is below every fixed-base exponential `c^n`, `c > 1`. -/
theorem isLittleO_nPowLog_const_exp {c : ℝ} (hc : 1 < c) :
    isLittleO nPowLog (fun n : ℕ => c ^ n) := by
  unfold isLittleO
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have hlogsq :
      (fun n : ℕ => Real.log (n : ℝ) ^ (2 : ℝ)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) :=
    isLittleO_log_rpow_rpow (a := 2) (r := 1) (by norm_num)
  have hbound := hlogsq.def (half_pos hlogc)
  have htend :
      Tendsto (fun n : ℕ => Real.log c * (n : ℝ) - Real.log (n : ℝ) ^ 2)
        atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hlogc))
    filter_upwards [hbound, eventually_ge_atTop 1] with n hn hnone
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
    simp only [Real.rpow_two, Real.rpow_one, Real.norm_eq_abs, abs_sq,
      abs_of_nonneg hnnonneg] at hn
    nlinarith
  have hexp :
      (fun n : ℕ => Real.exp (Real.log (n : ℝ) ^ 2)) =o[atTop]
        (fun n : ℕ => Real.exp (Real.log c * (n : ℝ))) := by
    rw [Real.isLittleO_exp_comp_exp_comp]
    exact htend
  refine hexp.congr' (Eventually.of_forall fun _ => rfl) ?_
  filter_upwards with n
  calc
    Real.exp (Real.log c * (n : ℝ)) = Real.exp ((n : ℝ) * Real.log c) := by rw [mul_comm]
    _ = Real.exp (Real.log c) ^ n := Real.exp_nat_mul (Real.log c) n
    _ = c ^ n := by rw [Real.exp_log (lt_trans zero_lt_one hc)]

/-- A single public bundle of the represented Chapter 3 growth hierarchy.

It retains the previously proved constant/logarithmic edges and adds the
fractional-power, `n^(log n)`, exponential, factorial, and self-power edges. -/
theorem complete_growth_hierarchy :
    isLittleO (fun n : ℕ => (lgStar n : ℝ)) (fun n => Real.log (n : ℝ)) ∧
    isLittleO (fun _ : ℕ => (1 : ℝ)) (fun n => Real.log (n : ℝ)) ∧
    isLittleO (fun n : ℕ => Real.log (Real.log (n : ℝ)))
      (fun n => Real.log (n : ℝ)) ∧
    isLittleO (fun n : ℕ => Real.log (n : ℝ)) (fun n => (n : ℝ)) ∧
    (∀ {a b : ℝ}, a < b →
      isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n => (n : ℝ) ^ b)) ∧
    (∀ a : ℝ, isLittleO (fun n : ℕ => (n : ℝ) ^ a) nPowLog) ∧
    isLittleO nPowLog (fun n : ℕ => (2 : ℝ) ^ n) ∧
    isLittleO (fun n : ℕ => (2 : ℝ) ^ n)
      (fun n => (Nat.factorial n : ℝ)) ∧
    isLittleO (fun n : ℕ => (Nat.factorial n : ℝ))
      (fun n => (n : ℝ) ^ n) := by
  exact ⟨isLittleO_lgStar_log, isLittleO_one_log, isLittleO_loglog_log,
    isLittleO_log_id, fun h => isLittleO_rpow_rpow h, isLittleO_rpow_nPowLog,
    isLittleO_nPowLog_const_exp (by norm_num), isLittleO_two_pow_factorial,
    isLittleO_factorial_pow_self⟩

end Chapter03
end CLRS
