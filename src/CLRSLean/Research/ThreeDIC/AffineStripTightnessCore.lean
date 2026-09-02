import CLRSLean.Research.ThreeDIC.AffineStripDefectLoad
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.CardIntervalMod

/-!
# Core affine-strip period arithmetic

This file contains index-space modular arithmetic only. It proves no physical
tightness by itself and makes no repairability or routing claim.
-/

namespace CLRS.Research.ThreeDIC

/-- The gcd condition saying that the two {name}`affineDirectionStep` values
jointly generate the full color residue group modulo {lit}`K`. By itself, this
condition does not assert {lit}`0 < K`. -/
def affineStripFullColorPeriod
    (alpha beta K : Nat) (along across : Nat × Nat) : Prop :=
  Nat.gcd
      (Nat.gcd K (affineDirectionStep alpha beta along))
      (affineDirectionStep alpha beta across) = 1

/-- The index pairs {lit}`(r, t)` counted for color {lit}`c`, where {lit}`r` is
the across-row index and {lit}`t` is the along-row index. The count retains
index multiplicity when different pairs have coincident physical
{name}`stripPoint` samples. -/
def affineStripColorIndexPairs
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter fun rt =>
    affineGridColor alpha beta gamma K
      (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c

/-- The cardinality of the affine-strip color index pairs, not the number of
distinct physical points. -/
def affineStripColorIndexCount
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Nat :=
  (affineStripColorIndexPairs alpha beta gamma K W L c
    base along across).card

private theorem affineGridColor_stripPoint_tightness
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

private theorem affineStripTightness_row_index_congruent
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
  rw [affineGridColor_stripPoint_tightness,
    affineGridColor_stripPoint_tightness] at hColor
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

/-- The fundamental {lit}`R`-by-{lit}`T` strip index cell. Its elements are
index pairs, not distinct physical points. -/
def affineStripFundamentalIndexPairs
    (alpha beta K : Nat) (along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  (Finset.range (affineStripAcrossPeriod alpha beta K along across)).product
    (Finset.range (affineLinePeriod alpha beta K along))

private theorem affineStripFundamentalColor_injOn
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    Set.InjOn
      (fun rt : Nat × Nat => affineGridColor alpha beta gamma K
        (stripPoint base along across rt.1 rt.2).1
        (stripPoint base along across rt.1 rt.2).2)
      (affineStripFundamentalIndexPairs alpha beta K along across) := by
  intro x hx y hy hColor
  obtain ⟨hxr, hxt⟩ := Finset.mem_product.mp hx
  obtain ⟨hyr, hyt⟩ := Finset.mem_product.mp hy
  have hRowMod :
      x.1 % affineStripAcrossPeriod alpha beta K along across =
        y.1 % affineStripAcrossPeriod alpha beta K along across :=
    affineStripTightness_row_index_congruent
      alpha beta gamma K base along across hK hColor
  have hRow : x.1 = y.1 := by
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hxr),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hyr)] at hRowMod
    exact hRowMod
  change
    affineGridColor alpha beta gamma K
        (linePoint (linePoint base across x.1) along x.2).1
        (linePoint (linePoint base across x.1) along x.2).2 =
      affineGridColor alpha beta gamma K
        (linePoint (linePoint base across y.1) along y.2).1
        (linePoint (linePoint base across y.1) along y.2).2 at hColor
  rw [← hRow] at hColor
  have hAlongMod :
      x.2 % affineLinePeriod alpha beta K along =
        y.2 % affineLinePeriod alpha beta K along :=
    affineGridColor_line_index_congruent
      alpha beta gamma K (linePoint base across x.1) along hK hColor
  have hAlong : x.2 = y.2 := by
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hxt),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hyt)] at hAlongMod
    exact hAlongMod
  exact Prod.ext hRow hAlong

/-- A full color period makes the cross-row period {lit}`R` times the along-row
period {lit}`T` equal {lit}`K`. The hypothesis {lit}`hK` is retained for the
public positive-modulus interface even though the pure divisibility identity
is algebraically stronger. -/
theorem affineStripPeriod_product_eq
    (alpha beta K : Nat) (along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    affineStripAcrossPeriod alpha beta K along across *
        affineLinePeriod alpha beta K along = K := by
  unfold affineStripFullColorPeriod at hFull
  unfold affineStripAcrossPeriod affineLinePeriod
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  have hgK : g ∣ K := Nat.gcd_dvd_left K _
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta along) hK
  change
    (g / Nat.gcd g (affineDirectionStep alpha beta across)) *
        (K / g) = K
  rw [hFull]
  simp only [Nat.div_one]
  obtain ⟨q, hKq⟩ := hgK
  calc
    g * (K / g) = g * ((g * q) / g) := by rw [hKq]
    _ = g * q := by rw [Nat.mul_div_cancel_left q hg]
    _ = K := hKq.symm

/-- Under the full-period hypothesis, every valid color occurs exactly once in
the fundamental strip index cell. -/
theorem affineStripFundamentalColor_image_eq_range
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    (affineStripFundamentalIndexPairs alpha beta K along across).image
        (fun rt => affineGridColor alpha beta gamma K
          (stripPoint base along across rt.1 rt.2).1
          (stripPoint base along across rt.1 rt.2).2) =
      Finset.range K := by
  apply Finset.eq_of_subset_of_card_le
  · intro c hc
    rw [Finset.mem_image] at hc
    obtain ⟨rt, _hrt, rfl⟩ := hc
    exact Finset.mem_range.mpr (Nat.mod_lt _ hK)
  · rw [Finset.card_range,
      Finset.card_image_iff.mpr
        (affineStripFundamentalColor_injOn
          alpha beta gamma K base along across hK)]
    unfold affineStripFundamentalIndexPairs
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
      Finset.card_range]
    exact (affineStripPeriod_product_eq
      alpha beta K along across hK hFull).ge

/-- On a rectangle aligned to both strip periods, each valid color has exactly
one index pair in every quotient block. This counts index pairs, not
deduplicated physical points. -/
theorem affineStripColorIndexCount_eq_of_period_dvd
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L) :
    affineStripColorIndexCount alpha beta gamma K W L c
        base along across =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) := by
  let R := affineStripAcrossPeriod alpha beta K along across
  let T := affineLinePeriod alpha beta K along
  have hR : 0 < R :=
    affineStripAcrossPeriod_pos alpha beta K along across hK
  have hT : 0 < T := affineLinePeriod_pos alpha beta K along hK
  have hInjective : Set.InjOn
      (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T))
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across) := by
    intro a ha b hb hab
    have hRowDiv := congrArg (fun p : Nat × Nat => p.1) hab
    have hAlongDiv := congrArg (fun p : Nat × Nat => p.2) hab
    change a.1 / R = b.1 / R at hRowDiv
    change a.2 / T = b.2 / T at hAlongDiv
    obtain ⟨_haRange, haColor⟩ := Finset.mem_filter.mp ha
    obtain ⟨_hbRange, hbColor⟩ := Finset.mem_filter.mp hb
    have hRowMod : a.1 % R = b.1 % R :=
      affineStripTightness_row_index_congruent
        alpha beta gamma K base along across hK
        (haColor.trans hbColor.symm)
    have hRow : a.1 = b.1 := by
      calc
        a.1 = a.1 % R + R * (a.1 / R) := (Nat.mod_add_div a.1 R).symm
        _ = b.1 % R + R * (b.1 / R) := by rw [hRowMod, hRowDiv]
        _ = b.1 := Nat.mod_add_div b.1 R
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
    have hAlong : a.2 = b.2 := by
      calc
        a.2 = a.2 % T + T * (a.2 / T) := (Nat.mod_add_div a.2 T).symm
        _ = b.2 % T + T * (b.2 / T) := by rw [hAlongMod, hAlongDiv]
        _ = b.2 := Nat.mod_add_div b.2 T
    exact Prod.ext hRow hAlong
  have hImageSubset :
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T)) ⊆
        (Finset.range (W / R)).product (Finset.range (L / T)) := by
    intro q hq
    obtain ⟨rt, hrt, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hrtRange, _hrtColor⟩ := Finset.mem_filter.mp hrt
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrtRange
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hR, Nat.div_mul_cancel hRW]
      exact Finset.mem_range.mp hr
    · apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hT, Nat.div_mul_cancel hTL]
      exact Finset.mem_range.mp ht
  have hImageSuperset :
      (Finset.range (W / R)).product (Finset.range (L / T)) ⊆
        (affineStripColorIndexPairs alpha beta gamma K W L c
          base along across).image
            (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T)) := by
    intro q hq
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hq
    let shiftedBase :=
      stripPoint base along across (R * q.1) (T * q.2)
    have hcImage :
        c ∈ (affineStripFundamentalIndexPairs alpha beta K
          along across).image
            (fun rt => affineGridColor alpha beta gamma K
              (stripPoint shiftedBase along across rt.1 rt.2).1
              (stripPoint shiftedBase along across rt.1 rt.2).2) := by
      rw [affineStripFundamentalColor_image_eq_range
        alpha beta gamma K shiftedBase along across hK hFull]
      exact Finset.mem_range.mpr hc
    obtain ⟨rt, hrtFund, hrtColor⟩ := Finset.mem_image.mp hcImage
    unfold affineStripFundamentalIndexPairs at hrtFund
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrtFund
    have hr0 : rt.1 < R := Finset.mem_range.mp hr
    have ht0 : rt.2 < T := Finset.mem_range.mp ht
    have hrBound : R * q.1 + rt.1 < W := by
      calc
        R * q.1 + rt.1 < R * q.1 + R := Nat.add_lt_add_left hr0 _
        _ = R * (q.1 + 1) := by ring
        _ ≤ R * (W / R) :=
          Nat.mul_le_mul_left R (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
        _ = W := Nat.mul_div_cancel' hRW
    have htBound : T * q.2 + rt.2 < L := by
      calc
        T * q.2 + rt.2 < T * q.2 + T := Nat.add_lt_add_left ht0 _
        _ = T * (q.2 + 1) := by ring
        _ ≤ T * (L / T) :=
          Nat.mul_le_mul_left T (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        _ = L := Nat.mul_div_cancel' hTL
    have hPoint :
        stripPoint base along across
            (R * q.1 + rt.1) (T * q.2 + rt.2) =
          stripPoint shiftedBase along across rt.1 rt.2 := by
      unfold shiftedBase stripPoint linePoint
      apply Prod.ext <;> simp only <;> ring
    apply Finset.mem_image.mpr
    refine ⟨(R * q.1 + rt.1, T * q.2 + rt.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hrBound, Finset.mem_range.mpr htBound⟩
      · rw [hPoint]
        exact hrtColor
    · apply Prod.ext
      · change (R * q.1 + rt.1) / R = q.1
        rw [Nat.mul_add_div hR, Nat.div_eq_of_lt hr0, Nat.add_zero]
      · change (T * q.2 + rt.2) / T = q.2
        rw [Nat.mul_add_div hT, Nat.div_eq_of_lt ht0, Nat.add_zero]
  have hImageEq :
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt : Nat × Nat => (rt.1 / R, rt.2 / T)) =
        (Finset.range (W / R)).product (Finset.range (L / T)) :=
    Finset.Subset.antisymm hImageSubset hImageSuperset
  unfold affineStripColorIndexCount
  change
    (affineStripColorIndexPairs alpha beta gamma K W L c
      base along across).card = (W / R) * (L / T)
  rw [← Finset.card_image_iff.mpr hInjective, hImageEq,
    Finset.product_eq_sprod, Finset.card_product, Finset.card_range,
    Finset.card_range]

end CLRS.Research.ThreeDIC
