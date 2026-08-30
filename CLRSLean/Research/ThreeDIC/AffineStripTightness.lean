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
