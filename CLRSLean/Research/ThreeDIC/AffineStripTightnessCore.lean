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

end CLRS.Research.ThreeDIC
