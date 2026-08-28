import CLRSLean.Research.ThreeDIC.WindowDiversity
import Mathlib.Data.Nat.ModEq

/-!
# Affine repair-chain colors along lattice-line defects

A lattice-line defect is sampled at natural indices from an origin and a
nonnegative integer direction.  Along such a line, the affine repair-chain
color is a modular arithmetic progression.  Its exact positive period is the
modulus divided by the greatest common divisor of the modulus and the color
step.

This module proves periodicity and the converse needed for counting: two line
indices of the same color are congruent modulo that period.  It does not make
claims about stochastic defect models or physical wire routing.
-/

namespace CLRS.Research.ThreeDIC

/-- The bump reached after {lit}`t` nonnegative lattice steps from
{lit}`base`. -/
def linePoint (base step : Nat × Nat) (t : Nat) : Nat × Nat :=
  (base.1 + step.1 * t, base.2 + step.2 * t)

/-- Change in the un-reduced affine color expression per lattice step. -/
def lineColorStep (M : Nat) (step : Nat × Nat) : Nat :=
  step.1 + M * step.2

/-- Fundamental period of affine colors along a lattice line. -/
def lineColorPeriod (M K : Nat) (step : Nat × Nat) : Nat :=
  K / Nat.gcd K (lineColorStep M step)

/-- A nonzero color modulus gives a positive line-color period, including for
the zero direction. -/
theorem lineColorPeriod_pos (M K : Nat) (step : Nat × Nat) (hK : 0 < K) :
    0 < lineColorPeriod M K step := by
  unfold lineColorPeriod
  exact Nat.div_pos
    (Nat.le_of_dvd hK (Nat.gcd_dvd_left K (lineColorStep M step)))
    (Nat.gcd_pos_of_pos_left (lineColorStep M step) hK)

/-- Along a lattice line, affine color is a modular arithmetic progression. -/
theorem affineChainColor_linePoint
    (M K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineChainColor M K (linePoint base step t).1 (linePoint base step t).2 =
      (base.1 + M * base.2 + lineColorStep M step * t) % K := by
  unfold affineChainColor linePoint lineColorStep
  congr 1
  ring

private theorem lineColorPeriod_multiple
    (M K : Nat) (step : Nat × Nat) :
    K ∣ lineColorStep M step * lineColorPeriod M K step := by
  let g := Nat.gcd K (lineColorStep M step)
  obtain ⟨q, hq⟩ : ∃ q, lineColorStep M step = g * q :=
    Nat.gcd_dvd_right K (lineColorStep M step)
  refine ⟨q, ?_⟩
  rw [hq]
  unfold lineColorPeriod
  change g * q * (K / g) = K * q
  calc
    g * q * (K / g) = (g * (K / g)) * q := by ac_rfl
    _ = K * q := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left K (lineColorStep M step))]

/-- Advancing by the fundamental line-color period preserves the affine
repair-chain color. -/
theorem lineColor_period
    (M K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineChainColor M K
        (linePoint base step (t + lineColorPeriod M K step)).1
        (linePoint base step (t + lineColorPeriod M K step)).2 =
      affineChainColor M K (linePoint base step t).1 (linePoint base step t).2 := by
  rw [affineChainColor_linePoint, affineChainColor_linePoint]
  have hStep :
      lineColorStep M step * (t + lineColorPeriod M K step) ≡
        lineColorStep M step * t [MOD K] := by
    change
      (lineColorStep M step * (t + lineColorPeriod M K step)) % K =
        (lineColorStep M step * t) % K
    rw [Nat.mul_add, Nat.add_mod, Nat.mod_eq_zero_of_dvd
      (lineColorPeriod_multiple M K step)]
    simp
  exact hStep.add_left (base.1 + M * base.2)

/-- Equal colors along one lattice line force equal index residues modulo the
fundamental period. -/
theorem lineColor_index_congruent
    (M K : Nat) (base step : Nat × Nat) (hK : 0 < K) {s t : Nat}
    (hColor :
      affineChainColor M K (linePoint base step s).1 (linePoint base step s).2 =
        affineChainColor M K (linePoint base step t).1 (linePoint base step t).2) :
    s % lineColorPeriod M K step = t % lineColorPeriod M K step := by
  rw [affineChainColor_linePoint, affineChainColor_linePoint] at hColor
  have hProgression :
      lineColorStep M step * s ≡ lineColorStep M step * t [MOD K] :=
    Nat.ModEq.add_left_cancel' (base.1 + M * base.2) hColor
  exact hProgression.cancel_left_div_gcd hK

end CLRS.Research.ThreeDIC
