import CLRSLean.Research.ThreeDIC.FiniteGrid
import CLRSLean.Research.ThreeDIC.LineDefectLoad
import Mathlib.Algebra.Order.Floor.Div

/-!
# Compositional load bounds for lattice strips

A physical strip is sampled by first advancing across rows and then along each
row.  The definitions below retain only the distinct physical points reached by
those samples.  Let {lit}`T = lineColorPeriod M K along` be the color period
within a row and {lit}`R = stripAcrossColorPeriod M K along across` the residual
row-index period after accounting for along-row color changes.  For any affine
repair-chain color, this module proves both the baseline bound
{lit}`W * ceil(L / T)` and the phase-aware bound
{lit}`ceil(W / R) * ceil(L / T)`.

These are upper bounds on the number of distinct physical color-{lit}`c`
points: coincident strip samples are deduplicated before their load is counted.
No tightness or end-to-end repairability claim is made.
-/

namespace CLRS.Research.ThreeDIC

/-- The physical point at row index {lit}`r` and along-row index {lit}`t`. -/
def stripPoint
    (base along across : Nat × Nat) (r t : Nat) : Nat × Nat :=
  linePoint (linePoint base across r) along t

/-- The distinct physical points sampled along row {lit}`r` of a strip. -/
def stripLinePoints
    (L : Nat) (base along across : Nat × Nat) (r : Nat) :
    Finset (Nat × Nat) :=
  (Finset.range L).image (stripPoint base along across r)

/-- The distinct physical points sampled by a width-{lit}`W`, length-{lit}`L`
strip. -/
def stripPoints
    (W L : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).image
    (fun rt => stripPoint base along across rt.1 rt.2)

/-- The distinct sampled strip points assigned affine repair-chain color
{lit}`c`. -/
def stripColorPoints
    (M K W L c : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  (stripPoints W L base along across).filter
    (fun p => affineChainColor M K p.1 p.2 = c)

/-- Fundamental row-index period remaining after quotienting out the color
change available along each row. -/
def stripAcrossColorPeriod
    (M K : Nat) (along across : Nat × Nat) : Nat :=
  let g := Nat.gcd K (lineColorStep M along)
  g / Nat.gcd g (lineColorStep M across)

/-- A nonzero color modulus gives a positive cross-line color period. -/
theorem stripAcrossColorPeriod_pos
    (M K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < stripAcrossColorPeriod M K along across := by
  let g := Nat.gcd K (lineColorStep M along)
  change 0 < g / Nat.gcd g (lineColorStep M across)
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (lineColorStep M along) hK
  exact Nat.div_pos
    (Nat.le_of_dvd hg (Nat.gcd_dvd_left g (lineColorStep M across)))
    (Nat.gcd_pos_of_pos_left (lineColorStep M across) hg)

/-- Affine strip colors form a two-dimensional modular arithmetic
progression. -/
private theorem affineChainColor_stripPoint
    (M K : Nat) (base along across : Nat × Nat) (r t : Nat) :
    affineChainColor M K (stripPoint base along across r t).1
      (stripPoint base along across r t).2 =
        (base.1 + M * base.2 + lineColorStep M across * r +
          lineColorStep M along * t) % K := by
  unfold affineChainColor stripPoint linePoint lineColorStep
  congr 1
  ring

/-- Equal strip colors force row indices to agree modulo the cross-line color
period, regardless of their positions along the two rows. -/
private theorem stripColor_row_index_congruent
    (M K : Nat) (base along across : Nat × Nat) (hK : 0 < K)
    {r s t u : Nat}
    (hColor :
      affineChainColor M K (stripPoint base along across r t).1
          (stripPoint base along across r t).2 =
        affineChainColor M K (stripPoint base along across s u).1
          (stripPoint base along across s u).2) :
    r % stripAcrossColorPeriod M K along across =
      s % stripAcrossColorPeriod M K along across := by
  rw [affineChainColor_stripPoint, affineChainColor_stripPoint] at hColor
  let g := Nat.gcd K (lineColorStep M along)
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (lineColorStep M along) hK
  have hColorG :
      base.1 + M * base.2 + lineColorStep M across * r +
          lineColorStep M along * t ≡
        base.1 + M * base.2 + lineColorStep M across * s +
          lineColorStep M along * u [MOD g] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_left K (lineColorStep M along)) hColor
  have hAlongDvd : g ∣ lineColorStep M along :=
    Nat.gcd_dvd_right K (lineColorStep M along)
  have hEraseT :
      base.1 + M * base.2 + lineColorStep M across * r +
          lineColorStep M along * t ≡
        base.1 + M * base.2 + lineColorStep M across * r [MOD g] := by
    simpa using
      (Nat.ModEq.add_left
        (base.1 + M * base.2 + lineColorStep M across * r)
        ((hAlongDvd.trans
          (Nat.dvd_mul_right (lineColorStep M along) t)).modEq_zero_nat))
  have hEraseU :
      base.1 + M * base.2 + lineColorStep M across * s +
          lineColorStep M along * u ≡
        base.1 + M * base.2 + lineColorStep M across * s [MOD g] := by
    simpa using
      (Nat.ModEq.add_left
        (base.1 + M * base.2 + lineColorStep M across * s)
        ((hAlongDvd.trans
          (Nat.dvd_mul_right (lineColorStep M along) u)).modEq_zero_nat))
  have hAcross :
      lineColorStep M across * r ≡ lineColorStep M across * s [MOD g] :=
    Nat.ModEq.add_left_cancel' (base.1 + M * base.2)
      (hEraseT.symm.trans (hColorG.trans hEraseU))
  change r ≡ s [MOD stripAcrossColorPeriod M K along across]
  simpa [stripAcrossColorPeriod, g] using
    hAcross.cancel_left_div_gcd hg

/-- Index pairs whose sampled physical point has affine color {lit}`c`. -/
private def stripColorIndexPairs
    (M K W L c : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter (fun rt =>
    affineChainColor M K (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c)

/-- Filtering distinct physical strip points is the image of filtering their
sample indices. -/
private theorem stripColorPoints_eq_image
    (M K W L c : Nat) (base along across : Nat × Nat) :
    stripColorPoints M K W L c base along across =
      (stripColorIndexPairs M K W L c base along across).image
        (fun rt => stripPoint base along across rt.1 rt.2) := by
  unfold stripColorPoints stripPoints stripColorIndexPairs
  rw [Finset.filter_image]

/-- A quotient of an index below {lit}`n` lies below the ceiling quotient. -/
private theorem quotient_lt_add_pred_div
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

/-- Equal quotient and remainder by the same divisor reconstruct equal natural
numbers. -/
private theorem eq_of_div_eq_of_mod_eq
    {a b d : Nat} (hdiv : a / d = b / d) (hmod : a % d = b % d) :
    a = b := by
  calc
    a = a % d + d * (a / d) := (Nat.mod_add_div a d).symm
    _ = b % d + d * (b / d) := by rw [hdiv, hmod]
    _ = b := Nat.mod_add_div b d

/-- The number of distinct color-{lit}`c` physical points in a strip is at
most the sum of the uniform per-row line bounds. -/
theorem stripColor_load_le_sum_lines
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      W * ((L + lineColorPeriod M K along - 1) /
        lineColorPeriod M K along) := by
  rw [stripColorPoints_eq_image]
  refine Finset.card_image_le.trans ?_
  let T := lineColorPeriod M K along
  change (stripColorIndexPairs M K W L c base along across).card ≤
    W * ((L + T - 1) / T)
  have hT : 0 < T := lineColorPeriod_pos M K along hK
  have hInjective : Set.InjOn
      (fun rt : Nat × Nat => (rt.1, rt.2 / T))
      (stripColorIndexPairs M K W L c base along across) := by
    intro a ha b hb hab
    change (a.1, a.2 / T) = (b.1, b.2 / T) at hab
    have hr := congrArg (fun p : Nat × Nat => p.1) hab
    have hdiv := congrArg (fun p : Nat × Nat => p.2) hab
    obtain ⟨_haRange, haColor⟩ := Finset.mem_filter.mp ha
    obtain ⟨_hbRange, hbColor⟩ := Finset.mem_filter.mp hb
    change affineChainColor M K
      (linePoint (linePoint base across a.1) along a.2).1
      (linePoint (linePoint base across a.1) along a.2).2 = c at haColor
    change affineChainColor M K
      (linePoint (linePoint base across b.1) along b.2).1
      (linePoint (linePoint base across b.1) along b.2).2 = c at hbColor
    rw [← hr] at hbColor
    have hmod : a.2 % T = b.2 % T :=
      lineColor_index_congruent M K (linePoint base across a.1) along hK
        (haColor.trans hbColor.symm)
    apply Prod.ext
    · exact hr
    · exact eq_of_div_eq_of_mod_eq hdiv hmod
  rw [← Finset.card_image_iff.mpr hInjective]
  have hImageRange :
      (stripColorIndexPairs M K W L c base along across).image
          (fun rt : Nat × Nat => (rt.1, rt.2 / T)) ⊆
        (Finset.range W).product (Finset.range ((L + T - 1) / T)) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨rt, hrt, rfl⟩ := hq
    obtain ⟨hrtRange, _hrtColor⟩ := Finset.mem_filter.mp hrt
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrtRange
    exact Finset.mem_product.mpr ⟨hr, Finset.mem_range.mpr
      (quotient_lt_add_pred_div hT (Finset.mem_range.mp ht))⟩
  calc
    ((stripColorIndexPairs M K W L c base along across).image
        (fun rt : Nat × Nat => (rt.1, rt.2 / T))).card ≤
        ((Finset.range W).product
          (Finset.range ((L + T - 1) / T))).card :=
      Finset.card_le_card hImageRange
    _ = W * ((L + T - 1) / T) := by
      rw [Finset.product_eq_sprod]
      simpa only [Finset.card_range] using
        Finset.card_product (Finset.range W)
          (Finset.range ((L + T - 1) / T))

/-- The number of distinct color-{lit}`c` physical points in a strip is at
most the product of the row- and along-index ceiling quotients determined by
the two phase periods. -/
theorem stripColor_load_le_phase_periods
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along) := by
  rw [stripColorPoints_eq_image]
  refine Finset.card_image_le.trans ?_
  let R := stripAcrossColorPeriod M K along across
  let T := lineColorPeriod M K along
  change (stripColorIndexPairs M K W L c base along across).card ≤
    ((W + R - 1) / R) * ((L + T - 1) / T)
  have hR : 0 < R := stripAcrossColorPeriod_pos M K along across hK
  have hT : 0 < T := lineColorPeriod_pos M K along hK
  have hInjective : Set.InjOn
      (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T))
      (stripColorIndexPairs M K W L c base along across) := by
    intro a ha b hb hab
    change (a.1 / R, a.2 / T) = (b.1 / R, b.2 / T) at hab
    have hRowDiv := congrArg (fun p : Nat × Nat => p.1) hab
    have hAlongDiv := congrArg (fun p : Nat × Nat => p.2) hab
    obtain ⟨_haRange, haColor⟩ := Finset.mem_filter.mp ha
    obtain ⟨_hbRange, hbColor⟩ := Finset.mem_filter.mp hb
    have hRowMod : a.1 % R = b.1 % R :=
      stripColor_row_index_congruent M K base along across hK
        (haColor.trans hbColor.symm)
    have hRow : a.1 = b.1 :=
      eq_of_div_eq_of_mod_eq hRowDiv hRowMod
    change affineChainColor M K
      (linePoint (linePoint base across a.1) along a.2).1
      (linePoint (linePoint base across a.1) along a.2).2 = c at haColor
    change affineChainColor M K
      (linePoint (linePoint base across b.1) along b.2).1
      (linePoint (linePoint base across b.1) along b.2).2 = c at hbColor
    rw [← hRow] at hbColor
    have hAlongMod : a.2 % T = b.2 % T :=
      lineColor_index_congruent M K (linePoint base across a.1) along hK
        (haColor.trans hbColor.symm)
    apply Prod.ext
    · exact hRow
    · exact eq_of_div_eq_of_mod_eq hAlongDiv hAlongMod
  rw [← Finset.card_image_iff.mpr hInjective]
  have hImageRange :
      (stripColorIndexPairs M K W L c base along across).image
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
          (quotient_lt_add_pred_div hR (Finset.mem_range.mp hr)),
        Finset.mem_range.mpr
          (quotient_lt_add_pred_div hT (Finset.mem_range.mp ht))⟩
  calc
    ((stripColorIndexPairs M K W L c base along across).image
        (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T))).card ≤
        ((Finset.range ((W + R - 1) / R)).product
          (Finset.range ((L + T - 1) / T))).card :=
      Finset.card_le_card hImageRange
    _ = ((W + R - 1) / R) * ((L + T - 1) / T) := by
      rw [Finset.product_eq_sprod]
      simpa only [Finset.card_range] using
        Finset.card_product (Finset.range ((W + R - 1) / R))
          (Finset.range ((L + T - 1) / T))

/-- A horizontal strip has one row phase and along-row period {lit}`K`. -/
theorem stripColor_horizontal_load_le
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card ≤
      W * ((L + K - 1) / K) := by
  simpa [stripAcrossColorPeriod, lineColorPeriod, lineColorStep] using
    stripColor_load_le_phase_periods M K W L c base (1, 0) (0, 1) hK

/-- A vertical strip has row phase period {lit}`gcd(K, M)` and along-row
period {lit}`K / gcd(K, M)`. -/
theorem stripColor_vertical_load_le_phase
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card ≤
      ((W + Nat.gcd K M - 1) / Nat.gcd K M) *
        ((L + K / Nat.gcd K M - 1) / (K / Nat.gcd K M)) := by
  simpa [stripAcrossColorPeriod, lineColorPeriod, lineColorStep] using
    stripColor_load_le_phase_periods M K W L c base (0, 1) (1, 0) hK

/-- The phase-aware strip bound with an explicit certificate that every
sample lies inside an {lit}`N x N` bump grid. -/
theorem stripColor_finiteGrid_load_le_phase_periods
    (N M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (_hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along) :=
  stripColor_load_le_phase_periods M K W L c base along across hK

end CLRS.Research.ThreeDIC
