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

end CLRS.Research.ThreeDIC
