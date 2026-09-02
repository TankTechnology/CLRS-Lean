import CLRSLean.Research.ThreeDIC.AffineLineDefectLoad
import CLRSLean.Research.ThreeDIC.StripDefectLoad
import Mathlib.Algebra.Order.Floor.Div

/-!
# Phase-aware strip bounds for parameterized affine colorings

This module lifts the physical finite-strip certificate from the fixed
mixed-radix coloring to {lit}`(alpha*i + beta*j + gamma) mod K`.  It counts unique
physical bump coordinates, derives both coefficient-sensitive phase periods,
and bounds one color load by {lit}`ceil(W/R) * ceil(L/T)`.

The result is an upper certificate.  It does not claim tightness, translated
window balance for arbitrary coefficients, physical routing, or repairability.
-/

namespace CLRS.Research.ThreeDIC

/-- Distinct sampled strip points assigned color {lit}`c` by a parameterized
affine coloring. -/
def affineStripColorPoints
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat) :=
  (stripPoints W L base along across).filter (fun p =>
    affineGridColor alpha beta gamma K p.1 p.2 = c)

/-- Fundamental cross-row period remaining after quotienting out the color
change available along a strip row. -/
def affineStripAcrossPeriod
    (alpha beta K : Nat) (along across : Nat × Nat) : Nat :=
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  g / Nat.gcd g (affineDirectionStep alpha beta across)

/-- A nonzero modulus gives a positive cross-row period. -/
theorem affineStripAcrossPeriod_pos
    (alpha beta K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < affineStripAcrossPeriod alpha beta K along across := by
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  change 0 < g / Nat.gcd g (affineDirectionStep alpha beta across)
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta along) hK
  exact Nat.div_pos
    (Nat.le_of_dvd hg
      (Nat.gcd_dvd_left g (affineDirectionStep alpha beta across)))
    (Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta across) hg)

private theorem affineGridColor_stripPoint
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (r t : Nat) :
    affineGridColor alpha beta gamma K
        (stripPoint base along across r t).1
        (stripPoint base along across r t).2 =
      (alpha * base.1 + beta * base.2 + gamma +
        affineDirectionStep alpha beta across * r +
        affineDirectionStep alpha beta along * t) % K := by
  unfold affineGridColor stripPoint linePoint affineDirectionStep
  congr 1
  ring

private theorem affineStripColor_row_index_congruent
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) {r s t u : Nat}
    (hColor :
      affineGridColor alpha beta gamma K
          (stripPoint base along across r t).1
          (stripPoint base along across r t).2 =
        affineGridColor alpha beta gamma K
          (stripPoint base along across s u).1
          (stripPoint base along across s u).2) :
    r % affineStripAcrossPeriod alpha beta K along across =
      s % affineStripAcrossPeriod alpha beta K along across := by
  rw [affineGridColor_stripPoint, affineGridColor_stripPoint] at hColor
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta along) hK
  have hColorG :
      alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * r +
          affineDirectionStep alpha beta along * t ≡
        alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * s +
          affineDirectionStep alpha beta along * u [MOD g] :=
    Nat.ModEq.of_dvd
      (Nat.gcd_dvd_left K (affineDirectionStep alpha beta along)) hColor
  have hAlongDvd : g ∣ affineDirectionStep alpha beta along :=
    Nat.gcd_dvd_right K (affineDirectionStep alpha beta along)
  have hEraseT :
      alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * r +
          affineDirectionStep alpha beta along * t ≡
        alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * r [MOD g] := by
    simpa using
      (Nat.ModEq.add_left
        (alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * r)
        ((hAlongDvd.trans
          (Nat.dvd_mul_right (affineDirectionStep alpha beta along) t)).modEq_zero_nat))
  have hEraseU :
      alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * s +
          affineDirectionStep alpha beta along * u ≡
        alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * s [MOD g] := by
    simpa using
      (Nat.ModEq.add_left
        (alpha * base.1 + beta * base.2 + gamma +
          affineDirectionStep alpha beta across * s)
        ((hAlongDvd.trans
          (Nat.dvd_mul_right (affineDirectionStep alpha beta along) u)).modEq_zero_nat))
  have hAcross :
      affineDirectionStep alpha beta across * r ≡
        affineDirectionStep alpha beta across * s [MOD g] :=
    Nat.ModEq.add_left_cancel'
      (alpha * base.1 + beta * base.2 + gamma)
      (hEraseT.symm.trans (hColorG.trans hEraseU))
  change r ≡ s [MOD affineStripAcrossPeriod alpha beta K along across]
  simpa [affineStripAcrossPeriod, g] using
    hAcross.cancel_left_div_gcd hg

private def affineStripColorIndexPairs
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter (fun rt =>
    affineGridColor alpha beta gamma K
      (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c)

private theorem affineStripColorPoints_eq_image
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) :
    affineStripColorPoints alpha beta gamma K W L c base along across =
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt => stripPoint base along across rt.1 rt.2) := by
  unfold affineStripColorPoints stripPoints affineStripColorIndexPairs
  rw [Finset.filter_image]

private theorem affineStripQuotient_lt_add_pred_div
    {x n d : Nat} (hd : 0 < d) (hx : x < n) :
    x / d < (n + d - 1) / d := by
  rw [Nat.div_lt_iff_lt_mul hd]
  have hCeil : n ≤ d * (n ⌈/⌉ d) :=
    (ceilDiv_le_iff_le_mul hd).1 le_rfl
  calc
    x < n := hx
    _ ≤ d * (n ⌈/⌉ d) := hCeil
    _ = (n + d - 1) / d * d := by
      rw [Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm]

private theorem affineStrip_eq_of_div_eq_of_mod_eq
    {a b d : Nat} (hdiv : a / d = b / d)
    (hmod : a % d = b % d) : a = b := by
  calc
    a = a % d + d * (a / d) := (Nat.mod_add_div a d).symm
    _ = b % d + d * (b / d) := by rw [hdiv, hmod]
    _ = b := Nat.mod_add_div b d

/-- The number of distinct physical points of one parameterized affine color
in a strip is at most the product of the cross-row and along-row ceiling
periods. -/
theorem affineStripColor_load_le_phase_periods
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along) := by
  rw [affineStripColorPoints_eq_image]
  refine Finset.card_image_le.trans ?_
  let R := affineStripAcrossPeriod alpha beta K along across
  let T := affineLinePeriod alpha beta K along
  change
    (affineStripColorIndexPairs alpha beta gamma K W L c
      base along across).card ≤
      ((W + R - 1) / R) * ((L + T - 1) / T)
  have hR : 0 < R :=
    affineStripAcrossPeriod_pos alpha beta K along across hK
  have hT : 0 < T := affineLinePeriod_pos alpha beta K along hK
  have hInjective : Set.InjOn
      (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T))
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across) := by
    intro a ha b hb hab
    change (a.1 / R, a.2 / T) = (b.1 / R, b.2 / T) at hab
    have hRowDiv := congrArg (fun p : Nat × Nat => p.1) hab
    have hAlongDiv := congrArg (fun p : Nat × Nat => p.2) hab
    obtain ⟨_haRange, haColor⟩ := Finset.mem_filter.mp ha
    obtain ⟨_hbRange, hbColor⟩ := Finset.mem_filter.mp hb
    have hRowMod : a.1 % R = b.1 % R :=
      affineStripColor_row_index_congruent
        alpha beta gamma K base along across hK
        (haColor.trans hbColor.symm)
    have hRow : a.1 = b.1 :=
      affineStrip_eq_of_div_eq_of_mod_eq hRowDiv hRowMod
    change affineGridColor alpha beta gamma K
      (linePoint (linePoint base across a.1) along a.2).1
      (linePoint (linePoint base across a.1) along a.2).2 = c at haColor
    change affineGridColor alpha beta gamma K
      (linePoint (linePoint base across b.1) along b.2).1
      (linePoint (linePoint base across b.1) along b.2).2 = c at hbColor
    rw [← hRow] at hbColor
    have hAlongMod : a.2 % T = b.2 % T :=
      affineGridColor_line_index_congruent
        alpha beta gamma K (linePoint base across a.1) along hK
        (haColor.trans hbColor.symm)
    apply Prod.ext
    · exact hRow
    · exact affineStrip_eq_of_div_eq_of_mod_eq hAlongDiv hAlongMod
  rw [← Finset.card_image_iff.mpr hInjective]
  have hImageRange :
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T)) ⊆
        (Finset.range ((W + R - 1) / R)).product
          (Finset.range ((L + T - 1) / T)) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨rt, hrt, rfl⟩ := hq
    obtain ⟨hrtRange, _hrtColor⟩ := Finset.mem_filter.mp hrt
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrtRange
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr
          (affineStripQuotient_lt_add_pred_div hR
            (Finset.mem_range.mp hr)),
        Finset.mem_range.mpr
          (affineStripQuotient_lt_add_pred_div hT
            (Finset.mem_range.mp ht))⟩
  calc
    ((affineStripColorIndexPairs alpha beta gamma K W L c
      base along across).image
        (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T))).card ≤
        ((Finset.range ((W + R - 1) / R)).product
          (Finset.range ((L + T - 1) / T))).card :=
      Finset.card_le_card hImageRange
    _ = ((W + R - 1) / R) * ((L + T - 1) / T) := by
      rw [Finset.product_eq_sprod]
      simpa only [Finset.card_range] using
        Finset.card_product (Finset.range ((W + R - 1) / R))
          (Finset.range ((L + T - 1) / T))

/-- The generalized phase-aware strip bound with an explicit finite-grid
domain certificate. -/
theorem affineStripColor_finiteGrid_load_le_phase_periods
    (N alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K)
    (_hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along) :=
  affineStripColor_load_le_phase_periods
    alpha beta gamma K W L c base along across hK

/-- The old fixed-color physical set is the {lit}`(1,M,0)` specialization. -/
theorem affineStripColorPoints_fixed_eq_stripColorPoints
    (M K W L c : Nat) (base along across : Nat × Nat) :
    affineStripColorPoints 1 M 0 K W L c base along across =
      stripColorPoints M K W L c base along across := by
  simp [affineStripColorPoints, stripColorPoints,
    affineGridColor_fixed_eq_affineChainColor]

/-- The old cross-row period is the {lit}`(1,M)` specialization. -/
theorem affineStripAcrossPeriod_fixed_eq_stripAcrossColorPeriod
    (M K : Nat) (along across : Nat × Nat) :
    affineStripAcrossPeriod 1 M K along across =
      stripAcrossColorPeriod M K along across := by
  simp [affineStripAcrossPeriod, stripAcrossColorPeriod,
    affineDirectionStep_fixed_eq_lineColorStep]

/-- The cross-row period is invariant under reducing both coefficients modulo
the color modulus. -/
theorem affineStripAcrossPeriod_mod_coefficients
    (alpha beta K : Nat) (along across : Nat × Nat) :
    affineStripAcrossPeriod (alpha % K) (beta % K) K along across =
      affineStripAcrossPeriod alpha beta K along across := by
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  have hAlong :
      Nat.gcd K
          (affineDirectionStep (alpha % K) (beta % K) along) = g := by
    simpa [g] using
      affineDirectionStep_gcd_mod_coefficients alpha beta K along
  have hAcrossMod :
      affineDirectionStep (alpha % K) (beta % K) across ≡
        affineDirectionStep alpha beta across [MOD g] :=
    (affineDirectionStep_mod_coefficients alpha beta K across).of_dvd
      (Nat.gcd_dvd_left K (affineDirectionStep alpha beta along))
  have hAcrossGcd :
      Nat.gcd g
          (affineDirectionStep (alpha % K) (beta % K) across) =
        Nat.gcd g (affineDirectionStep alpha beta across) := by
    have hGcd := hAcrossMod.gcd_eq
    simpa only [Nat.gcd_comm] using hGcd
  unfold affineStripAcrossPeriod
  change
    Nat.gcd K (affineDirectionStep (alpha % K) (beta % K) along) /
        Nat.gcd
          (Nat.gcd K
            (affineDirectionStep (alpha % K) (beta % K) along))
          (affineDirectionStep (alpha % K) (beta % K) across) =
      g / Nat.gcd g (affineDirectionStep alpha beta across)
  rw [hAlong, hAcrossGcd]

end CLRS.Research.ThreeDIC
