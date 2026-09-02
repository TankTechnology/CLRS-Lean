import CLRSLean.Research.ThreeDIC.AffineStripTightness

open CLRS.Research.ThreeDIC

#check affineStripFullColorPeriod
#check affineStripColorIndexPairs
#check affineStripColorIndexCount
#check affineStripPeriod_product_eq
#check affineStripFundamentalIndexPairs
#check affineStripFundamentalColor_image_eq_range
#check affineStripColorIndexCount_eq_of_period_dvd
#check affineStripSamplingInjective
#check affineStripSamplingInjective_axisAligned
#check affineStripSamplingInjective_axisAlignedSwapped
#check affineStripColorPoints_card_eq_indexCount
#check affineStripColor_load_eq_of_period_dvd
#check affineStripColor_load_eq_phase_periods
#check affineStripColor_axisAligned_load_eq_phase_periods
#check affineStripColor_axisAlignedSwapped_load_eq_phase_periods
#check stripColor_horizontal_load_eq
#check stripColor_vertical_load_eq_phase

example
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    (affineStripFundamentalIndexPairs alpha beta K along across).image
        (fun rt => affineGridColor alpha beta gamma K
          (stripPoint base along across rt.1 rt.2).1
          (stripPoint base along across rt.1 rt.2).2) =
      Finset.range K :=
  affineStripFundamentalColor_image_eq_range
    alpha beta gamma K base along across hK hFull

example
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L) :
    affineStripColorIndexCount alpha beta gamma K W L c
        base along across =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) :=
  affineStripColorIndexCount_eq_of_period_dvd
    alpha beta gamma K W L c base along across hK hc hFull hRW hTL

example
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c base along across).card =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) :=
  affineStripColor_load_eq_of_period_dvd
    alpha beta gamma K W L c base along across
      hK hc hFull hRW hTL hInjective

example
    (alpha beta gamma K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta)
    (hRW : affineStripAcrossPeriod alpha beta K (1, 0) (0, 1) ∣ W)
    (hTL : affineLinePeriod alpha beta K (1, 0) ∣ L) :
    (affineStripColorPoints alpha beta gamma K W L c
      base (1, 0) (0, 1)).card =
      (W / affineStripAcrossPeriod alpha beta K (1, 0) (0, 1)) *
        (L / affineLinePeriod alpha beta K (1, 0)) :=
  affineStripColor_axisAligned_load_eq_phase_periods
    alpha beta gamma K W L c base hK hc hUnit hRW hTL

example
    (alpha beta gamma K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta)
    (hRW : affineStripAcrossPeriod alpha beta K (0, 1) (1, 0) ∣ W)
    (hTL : affineLinePeriod alpha beta K (0, 1) ∣ L) :
    (affineStripColorPoints alpha beta gamma K W L c
      base (0, 1) (1, 0)).card =
      (W / affineStripAcrossPeriod alpha beta K (0, 1) (1, 0)) *
        (L / affineLinePeriod alpha beta K (0, 1)) :=
  affineStripColor_axisAlignedSwapped_load_eq_phase_periods
    alpha beta gamma K W L c base hK hc hUnit hRW hTL

example
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K) (hKL : K ∣ L) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card =
      W * (L / K) :=
  stripColor_horizontal_load_eq M K W L c base hK hc hKL

example
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hRW : Nat.gcd K M ∣ W)
    (hTL : K / Nat.gcd K M ∣ L) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card =
      (W / Nat.gcd K M) * (L / (K / Nat.gcd K M)) :=
  stripColor_vertical_load_eq_phase M K W L c base hK hc hRW hTL

example :
    (stripColorPoints 3 1 4 5 0 (0, 0) (1, 0) (0, 1)).card = 20 := by
  decide

example :
    (stripColorPoints 3 7 0 5 0 (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (stripColorPoints 2 8 4 0 0 (0, 0) (0, 1) (1, 0)).card = 0 := by
  decide

example :
    (stripColorPoints 2 8 4 4 0 (0, 0) (0, 1) (1, 0)).card = 2 := by
  decide

example :
    affineStripColorIndexCount 1 0 0 2 2 2 1
        (0, 0) (1, 0) (1, 0) = 2 := by
  decide

example :
    (affineStripColorPoints 1 0 0 2 2 2 1
      (0, 0) (1, 0) (1, 0)).card = 1 := by
  decide
