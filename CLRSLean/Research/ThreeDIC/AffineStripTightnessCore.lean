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

def affineStripFullColorPeriod
    (alpha beta K : Nat) (along across : Nat × Nat) : Prop :=
  Nat.gcd
      (Nat.gcd K (affineDirectionStep alpha beta along))
      (affineDirectionStep alpha beta across) = 1

def affineStripColorIndexPairs
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter fun rt =>
    affineGridColor alpha beta gamma K
      (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c

def affineStripColorIndexCount
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Nat :=
  (affineStripColorIndexPairs alpha beta gamma K W L c
    base along across).card

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
  change
    (g / Nat.gcd g (affineDirectionStep alpha beta across)) *
        (K / g) = K
  rw [hFull]
  simp only [Nat.div_one]
  exact Nat.mul_div_cancel' hgK

end CLRS.Research.ThreeDIC
