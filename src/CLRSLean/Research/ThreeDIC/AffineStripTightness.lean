import CLRSLean.Research.ThreeDIC.AffineStripTightnessCore

/-!
# Exact physical affine-strip load under no overlap

This file bridges affine-strip index multiplicity to deduplicated physical
points under an explicit no-overlap hypothesis. The exact load formulas are
conditional on positive-modulus, valid-color, full-period, aligned-divisibility,
and sampling-injectivity assumptions; they make no universal tightness,
routing, repairability, spare, or mux claim.
-/

namespace CLRS.Research.ThreeDIC

/-- Distinct valid {lit}`(r, t)` samples name distinct physical bumps throughout
the requested {lit}`W`-by-{lit}`L` strip index rectangle. -/
def affineStripSamplingInjective
    (W L : Nat) (base along across : Nat × Nat) : Prop :=
  Set.InjOn
    (fun rt : Nat × Nat => stripPoint base along across rt.1 rt.2)
    ((Finset.range W).product (Finset.range L))

/-- Axis-aligned strip sampling is injective for every width and length: the
physical first coordinate recovers the along index, and the physical second
coordinate recovers the across-row index. -/
theorem affineStripSamplingInjective_axisAligned
    (W L : Nat) (base : Nat × Nat) :
    affineStripSamplingInjective W L base (1, 0) (0, 1) := by
  intro ⟨r, t⟩ _ ⟨s, u⟩ _ hPoint
  unfold stripPoint linePoint at hPoint
  simp only [zero_mul, one_mul, Nat.add_zero] at hPoint
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.snd hPoint)
  · exact Nat.add_left_cancel (congrArg Prod.fst hPoint)

/-- Swapped axis-aligned strip sampling is injective for every width and
length: the physical first coordinate recovers the across-row index, and the
physical second coordinate recovers the along index. -/
theorem affineStripSamplingInjective_axisAlignedSwapped
    (W L : Nat) (base : Nat × Nat) :
    affineStripSamplingInjective W L base (0, 1) (1, 0) := by
  intro ⟨r, t⟩ _ ⟨s, u⟩ _ hPoint
  unfold stripPoint linePoint at hPoint
  simp only [zero_mul, one_mul, Nat.add_zero] at hPoint
  apply Prod.ext
  · exact Nat.add_left_cancel (congrArg Prod.fst hPoint)
  · exact Nat.add_left_cancel (congrArg Prod.snd hPoint)

/-- A unit affine coefficient gives the full color period for the standard
axis-aligned strip orientation. -/
private theorem affineStripFullColorPeriod_axisAligned
    (alpha beta K : Nat)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineStripFullColorPeriod alpha beta K (1, 0) (0, 1) := by
  rcases hUnit with hAlpha | hBeta
  · simp [affineStripFullColorPeriod, affineDirectionStep, hAlpha]
  · unfold affineStripFullColorPeriod
    simpa [affineDirectionStep] using
      (Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left K alpha) hBeta)

/-- A unit affine coefficient gives the full color period for the swapped
axis-aligned strip orientation. -/
private theorem affineStripFullColorPeriod_axisAlignedSwapped
    (alpha beta K : Nat)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineStripFullColorPeriod alpha beta K (0, 1) (1, 0) := by
  rcases hUnit with hAlpha | hBeta
  · unfold affineStripFullColorPeriod
    simpa [affineDirectionStep] using
      (Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left K beta) hAlpha)
  · simp [affineStripFullColorPeriod, affineDirectionStep, hBeta]

private theorem affineStripColorPoints_eq_tightness_image
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) :
    affineStripColorPoints alpha beta gamma K W L c base along across =
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt => stripPoint base along across rt.1 rt.2) := by
  unfold affineStripColorPoints stripPoints affineStripColorIndexPairs
  rw [Finset.filter_image]

/-- Under the explicit sampling-injectivity hypothesis, filtering by one color
does not collapse any remaining index pair, so the number of deduplicated
physical points equals the color index count. This bridge requires no period
alignment and makes no unconditional tightness claim. -/
theorem affineStripColorPoints_card_eq_indexCount
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      affineStripColorIndexCount alpha beta gamma K W L c
        base along across := by
  rw [affineStripColorPoints_eq_tightness_image]
  unfold affineStripColorIndexCount
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  apply hInjective
  · exact (Finset.mem_filter.mp ha).1
  · exact (Finset.mem_filter.mp hb).1
  · exact hab

/-- If the color modulus is positive, the requested color is valid, the two
strip periods jointly cover the full color period, both rectangle dimensions
are aligned to their respective periods, and valid samples name distinct
physical bumps, then the physical color load is exactly the quotient-block
count. This is an aligned conditional equality, not universal tightness. -/
theorem affineStripColor_load_eq_of_period_dvd
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) := by
  calc
    (affineStripColorPoints alpha beta gamma K W L c
        base along across).card =
        affineStripColorIndexCount alpha beta gamma K W L c
          base along across :=
      affineStripColorPoints_card_eq_indexCount
        alpha beta gamma K W L c base along across hInjective
    _ =
        (W / affineStripAcrossPeriod alpha beta K along across) *
          (L / affineLinePeriod alpha beta K along) :=
      affineStripColorIndexCount_eq_of_period_dvd
        alpha beta gamma K W L c base along across
          hK hc hFull hRW hTL

/-- For axis-aligned sampling, if the positive modulus has a valid requested
color and at least one affine coefficient is coprime to the modulus, then
width divisibility by the across period and length divisibility by the line
period give the exact physical quotient-block load. Axis alignment discharges
sampling injectivity; this theorem does not cover partial-period or
self-intersecting strips. -/
theorem affineStripColor_axisAligned_load_eq_phase_periods
    (alpha beta gamma K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta)
    (hRW : affineStripAcrossPeriod alpha beta K (1, 0) (0, 1) ∣ W)
    (hTL : affineLinePeriod alpha beta K (1, 0) ∣ L) :
    (affineStripColorPoints alpha beta gamma K W L c
      base (1, 0) (0, 1)).card =
      (W / affineStripAcrossPeriod alpha beta K (1, 0) (0, 1)) *
        (L / affineLinePeriod alpha beta K (1, 0)) :=
  affineStripColor_load_eq_of_period_dvd
    alpha beta gamma K W L c base (1, 0) (0, 1)
      hK hc (affineStripFullColorPeriod_axisAligned alpha beta K hUnit)
      hRW hTL (affineStripSamplingInjective_axisAligned W L base)

/-- For swapped axis-aligned sampling, if the positive modulus has a valid
requested color and at least one affine coefficient is coprime to the modulus,
then width divisibility by the across period and length divisibility by the
line period give the exact physical quotient-block load. Swapped axis
alignment discharges sampling injectivity; this theorem does not cover
partial-period or self-intersecting strips. -/
theorem affineStripColor_axisAlignedSwapped_load_eq_phase_periods
    (alpha beta gamma K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta)
    (hRW : affineStripAcrossPeriod alpha beta K (0, 1) (1, 0) ∣ W)
    (hTL : affineLinePeriod alpha beta K (0, 1) ∣ L) :
    (affineStripColorPoints alpha beta gamma K W L c
      base (0, 1) (1, 0)).card =
      (W / affineStripAcrossPeriod alpha beta K (0, 1) (1, 0)) *
        (L / affineLinePeriod alpha beta K (0, 1)) :=
  affineStripColor_load_eq_of_period_dvd
    alpha beta gamma K W L c base (0, 1) (1, 0)
      hK hc (affineStripFullColorPeriod_axisAlignedSwapped alpha beta K hUnit)
      hRW hTL (affineStripSamplingInjective_axisAlignedSwapped W L base)

/-- For the fixed coloring on a horizontal axis-aligned strip, a positive
modulus, valid color, and exact divisibility {lit}`K ∣ L` give physical load
{lit}`W * (L / K)`. This aligned result includes zero width but does not cover
partial-period lengths or self-intersecting sampling directions. -/
theorem stripColor_horizontal_load_eq
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K) (hKL : K ∣ L) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card =
      W * (L / K) := by
  rw [← affineStripColorPoints_fixed_eq_stripColorPoints]
  simpa [affineStripAcrossPeriod, affineLinePeriod, affineDirectionStep] using
    (affineStripColor_axisAligned_load_eq_phase_periods
      1 M 0 K W L c base hK hc (Or.inl (Nat.coprime_one_right K))
      (by simp [affineStripAcrossPeriod, affineDirectionStep])
      (by simpa [affineLinePeriod, affineDirectionStep] using hKL))

/-- For the fixed coloring on a vertical swapped-axis strip, a positive
modulus, valid color, width divisibility by {lit}`gcd K M`, and length
divisibility by {lit}`K / gcd K M` give the exact physical phase-period load.
This aligned result includes zero dimensions but does not cover partial-period
or self-intersecting sampling directions. -/
theorem stripColor_vertical_load_eq_phase
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hRW : Nat.gcd K M ∣ W)
    (hTL : K / Nat.gcd K M ∣ L) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card =
      (W / Nat.gcd K M) * (L / (K / Nat.gcd K M)) := by
  rw [← affineStripColorPoints_fixed_eq_stripColorPoints]
  simpa [affineStripAcrossPeriod, affineLinePeriod, affineDirectionStep] using
    (affineStripColor_axisAlignedSwapped_load_eq_phase_periods
      1 M 0 K W L c base hK hc (Or.inl (Nat.coprime_one_right K))
      (by
        simpa [affineStripAcrossPeriod, affineDirectionStep] using hRW)
      (by simpa [affineLinePeriod, affineDirectionStep] using hTL))

/-- Under the same positive-modulus, valid-color, full-period, aligned-window,
and no-overlap assumptions as {name}`affineStripColor_load_eq_of_period_dvd`,
the exact physical load also matches the phase-period ceiling expression used
by the general upper bound. Alignment makes each ceiling an ordinary quotient;
this remains a conditional equality and does not assert universal tightness. -/
theorem affineStripColor_load_eq_phase_periods
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along) := by
  let R := affineStripAcrossPeriod alpha beta K along across
  let T := affineLinePeriod alpha beta K along
  have hR : 0 < R := by
    simpa [R] using
      affineStripAcrossPeriod_pos alpha beta K along across hK
  have hT : 0 < T := by
    simpa [T] using affineLinePeriod_pos alpha beta K along hK
  have hRW' : R ∣ W := by simpa [R] using hRW
  have hTL' : T ∣ L := by simpa [T] using hTL
  have hWCeil : (W + R - 1) / R = W / R := by
    obtain ⟨q, rfl⟩ := hRW'
    rw [← Nat.ceilDiv_eq_add_pred_div, Nat.mul_div_cancel_left q hR]
    simpa only [nsmul_eq_mul, Nat.cast_id] using
      (smul_ceilDiv (α := Nat) (β := Nat) hR q)
  have hLCeil : (L + T - 1) / T = L / T := by
    obtain ⟨q, rfl⟩ := hTL'
    rw [← Nat.ceilDiv_eq_add_pred_div, Nat.mul_div_cancel_left q hT]
    simpa only [nsmul_eq_mul, Nat.cast_id] using
      (smul_ceilDiv (α := Nat) (β := Nat) hT q)
  change
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      ((W + R - 1) / R) * ((L + T - 1) / T)
  calc
    (affineStripColorPoints alpha beta gamma K W L c
        base along across).card =
        (W / R) * (L / T) := by
      simpa [R, T] using
        affineStripColor_load_eq_of_period_dvd
          alpha beta gamma K W L c base along across
            hK hc hFull hRW hTL hInjective
    _ = ((W + R - 1) / R) * ((L + T - 1) / T) := by
      rw [hWCeil, hLCeil]

end CLRS.Research.ThreeDIC
