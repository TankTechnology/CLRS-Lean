import CLRSLean.Research.ThreeDIC.LineDefect
import Mathlib.Data.Nat.ModEq

/-!
# Parameterized affine colorings on a bump grid

This module generalizes the fixed mixed-radix repair-chain coloring to
{lit}`(alpha * i + beta * j + gamma) mod K`.  Along any nonnegative lattice
direction the colors form a modular arithmetic progression whose exact index
period is the modulus divided by the gcd of the modulus and the directional
step.

The additive offset changes color labels but not any directional period.  No
window-balance, routing, or repairability property is asserted for arbitrary
coefficients.
-/

namespace CLRS.Research.ThreeDIC

/-- Parameterized affine color of bump coordinate {lit}`(i,j)`. -/
def affineGridColor
    (alpha beta gamma K i j : Nat) : Nat :=
  (alpha * i + beta * j + gamma) % K

/-- Change in the unreduced affine expression along one lattice step. -/
def affineDirectionStep
    (alpha beta : Nat) (step : Nat × Nat) : Nat :=
  alpha * step.1 + beta * step.2

/-- Fundamental index period of a parameterized affine color along a line. -/
def affineLinePeriod
    (alpha beta K : Nat) (step : Nat × Nat) : Nat :=
  K / Nat.gcd K (affineDirectionStep alpha beta step)

/-- A nonzero modulus gives a positive affine line period, including for a
zero direction. -/
theorem affineLinePeriod_pos
    (alpha beta K : Nat) (step : Nat × Nat) (hK : 0 < K) :
    0 < affineLinePeriod alpha beta K step := by
  unfold affineLinePeriod
  exact Nat.div_pos
    (Nat.le_of_dvd hK
      (Nat.gcd_dvd_left K (affineDirectionStep alpha beta step)))
    (Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta step) hK)

/-- Along a lattice line, a parameterized affine color is a modular
arithmetic progression. -/
theorem affineGridColor_linePoint
    (alpha beta gamma K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineGridColor alpha beta gamma K
        (linePoint base step t).1 (linePoint base step t).2 =
      (alpha * base.1 + beta * base.2 + gamma +
        affineDirectionStep alpha beta step * t) % K := by
  unfold affineGridColor linePoint affineDirectionStep
  congr 1
  ring

private theorem affineLinePeriod_multiple
    (alpha beta K : Nat) (step : Nat × Nat) :
    K ∣ affineDirectionStep alpha beta step *
      affineLinePeriod alpha beta K step := by
  let g := Nat.gcd K (affineDirectionStep alpha beta step)
  obtain ⟨q, hq⟩ :
      ∃ q, affineDirectionStep alpha beta step = g * q :=
    Nat.gcd_dvd_right K (affineDirectionStep alpha beta step)
  refine ⟨q, ?_⟩
  rw [hq]
  unfold affineLinePeriod
  change g * q * (K / g) = K * q
  calc
    g * q * (K / g) = (g * (K / g)) * q := by ac_rfl
    _ = K * q := by
      rw [Nat.mul_div_cancel'
        (Nat.gcd_dvd_left K (affineDirectionStep alpha beta step))]

/-- Advancing by the fundamental line period preserves the affine color. -/
theorem affineGridColor_line_periodic
    (alpha beta gamma K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineGridColor alpha beta gamma K
        (linePoint base step (t + affineLinePeriod alpha beta K step)).1
        (linePoint base step (t + affineLinePeriod alpha beta K step)).2 =
      affineGridColor alpha beta gamma K
        (linePoint base step t).1 (linePoint base step t).2 := by
  rw [affineGridColor_linePoint, affineGridColor_linePoint]
  have hStep :
      affineDirectionStep alpha beta step *
          (t + affineLinePeriod alpha beta K step) ≡
        affineDirectionStep alpha beta step * t [MOD K] := by
    change
      (affineDirectionStep alpha beta step *
          (t + affineLinePeriod alpha beta K step)) % K =
        (affineDirectionStep alpha beta step * t) % K
    rw [Nat.mul_add, Nat.add_mod, Nat.mod_eq_zero_of_dvd
      (affineLinePeriod_multiple alpha beta K step)]
    simp
  exact hStep.add_left (alpha * base.1 + beta * base.2 + gamma)

/-- Equal colors on one lattice line force equal index residues modulo the
fundamental affine line period. -/
theorem affineGridColor_line_index_congruent
    (alpha beta gamma K : Nat) (base step : Nat × Nat) (hK : 0 < K)
    {s t : Nat}
    (hColor :
      affineGridColor alpha beta gamma K
          (linePoint base step s).1 (linePoint base step s).2 =
        affineGridColor alpha beta gamma K
          (linePoint base step t).1 (linePoint base step t).2) :
    s % affineLinePeriod alpha beta K step =
      t % affineLinePeriod alpha beta K step := by
  rw [affineGridColor_linePoint, affineGridColor_linePoint] at hColor
  have hProgression :
      affineDirectionStep alpha beta step * s ≡
        affineDirectionStep alpha beta step * t [MOD K] :=
    Nat.ModEq.add_left_cancel'
      (alpha * base.1 + beta * base.2 + gamma) hColor
  exact hProgression.cancel_left_div_gcd hK

/-- The original mixed-radix color is the {lit}`(1,M,0)` specialization. -/
theorem affineGridColor_fixed_eq_affineChainColor
    (M K i j : Nat) :
    affineGridColor 1 M 0 K i j = affineChainColor M K i j := by
  simp [affineGridColor, affineChainColor]

/-- The original directional step is the {lit}`(1,M)` specialization. -/
theorem affineDirectionStep_fixed_eq_lineColorStep
    (M : Nat) (step : Nat × Nat) :
    affineDirectionStep 1 M step = lineColorStep M step := by
  simp [affineDirectionStep, lineColorStep]

/-- The original line period is the {lit}`(1,M)` specialization. -/
theorem affineLinePeriod_fixed_eq_lineColorPeriod
    (M K : Nat) (step : Nat × Nat) :
    affineLinePeriod 1 M K step = lineColorPeriod M K step := by
  simp [affineLinePeriod, lineColorPeriod,
    affineDirectionStep_fixed_eq_lineColorStep]

/-- Reducing both affine coefficients modulo the color modulus preserves the
directional step modulo that modulus. -/
theorem affineDirectionStep_mod_coefficients
    (alpha beta K : Nat) (step : Nat × Nat) :
    affineDirectionStep (alpha % K) (beta % K) step ≡
      affineDirectionStep alpha beta step [MOD K] := by
  unfold affineDirectionStep
  exact ((Nat.mod_modEq alpha K).mul_right step.1).add
    ((Nat.mod_modEq beta K).mul_right step.2)

/-- The directional gcd, and hence every period derived from it, depends only
on coefficient residues modulo {lit}`K`. -/
theorem affineDirectionStep_gcd_mod_coefficients
    (alpha beta K : Nat) (step : Nat × Nat) :
    Nat.gcd K (affineDirectionStep (alpha % K) (beta % K) step) =
      Nat.gcd K (affineDirectionStep alpha beta step) := by
  have hGcd :=
    (affineDirectionStep_mod_coefficients alpha beta K step).gcd_eq
  simpa only [Nat.gcd_comm] using hGcd

/-- The exact affine line period is invariant under coefficient reduction
modulo {lit}`K`. -/
theorem affineLinePeriod_mod_coefficients
    (alpha beta K : Nat) (step : Nat × Nat) :
    affineLinePeriod (alpha % K) (beta % K) K step =
      affineLinePeriod alpha beta K step := by
  unfold affineLinePeriod
  rw [affineDirectionStep_gcd_mod_coefficients]

end CLRS.Research.ThreeDIC
