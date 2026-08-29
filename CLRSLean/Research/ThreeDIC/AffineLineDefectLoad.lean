import CLRSLean.Research.ThreeDIC.AffineColoring
import CLRSLean.Research.ThreeDIC.FiniteGrid
import CLRSLean.Research.ThreeDIC.LineDefectLoad
import Mathlib.Algebra.Order.Floor.Div

/-!
# Load bounds for parameterized affine lattice-line defects

For a finite line prefix, this module counts the sample indices assigned one
parameterized affine color.  Equal-colored indices lie in one residue class
modulo the exact affine line period, so quotienting by the period gives the
same ceiling bound as for the fixed mixed-radix coloring.

The theorem is deterministic and coefficient-sensitive.  It does not assert
window balance, physical routing, or repair success.
-/

namespace CLRS.Research.ThreeDIC

/-- Indices below {lit}`L` on a lattice line that receive color {lit}`c`
under a parameterized affine coloring. -/
def affineLineColorIndices
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat) : Finset Nat :=
  (Finset.range L).filter (fun t =>
    affineGridColor alpha beta gamma K
      (linePoint base step t).1 (linePoint base step t).2 = c)

private theorem affineQuotient_lt_ceilDiv
    {t L T : Nat} (hT : 0 < T) (ht : t < L) :
    t / T < (L + T - 1) / T := by
  rw [Nat.div_lt_iff_lt_mul hT]
  have hCeil : L ≤ T * (L ⌈/⌉ T) :=
    (ceilDiv_le_iff_le_mul hT).1 le_rfl
  calc
    t < L := ht
    _ ≤ T * (L ⌈/⌉ T) := hCeil
    _ = (L + T - 1) / T * T := by
      rw [Nat.ceilDiv_eq_add_pred_div, Nat.mul_comm]

private theorem affineCard_le_ceilDiv_of_mod_eq
    (s : Finset Nat) {L T : Nat} (hT : 0 < T)
    (hRange : s ⊆ Finset.range L)
    (hMod : ∀ a ∈ s, ∀ b ∈ s, a % T = b % T) :
    s.card ≤ (L + T - 1) / T := by
  classical
  have hInjective : Set.InjOn (fun t : Nat => t / T) s := by
    intro a ha b hb hab
    change a / T = b / T at hab
    calc
      a = a % T + T * (a / T) := (Nat.mod_add_div a T).symm
      _ = b % T + T * (b / T) := by rw [hMod a ha b hb, hab]
      _ = b := Nat.mod_add_div b T
  rw [← Finset.card_image_iff.mpr hInjective]
  have hImageRange :
      s.image (fun t => t / T) ⊆ Finset.range ((L + T - 1) / T) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    rw [Finset.mem_range]
    exact affineQuotient_lt_ceilDiv hT
      (Finset.mem_range.mp (hRange ht))
  simpa only [Finset.card_range] using Finset.card_le_card hImageRange

/-- A color occurs at most {lit}`ceil(L/T)` times in a finite line prefix,
where {lit}`T` is the exact coefficient-sensitive line period. -/
theorem affineLineColor_load_le_ceilDiv_period
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step := by
  apply affineCard_le_ceilDiv_of_mod_eq
    (affineLineColorIndices alpha beta gamma K L c base step)
    (affineLinePeriod_pos alpha beta K step hK)
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro s hs t ht
    exact affineGridColor_line_index_congruent
      alpha beta gamma K base step hK
      ((Finset.mem_filter.mp hs).2.trans
        (Finset.mem_filter.mp ht).2.symm)

/-- A direction whose affine step is coprime to the modulus visits every
residue before repeating. -/
theorem affineLineColor_coprime_load_le
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (hCoprime : Nat.Coprime K (affineDirectionStep alpha beta step)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + K - 1) / K := by
  simpa [affineLinePeriod, hCoprime] using
    affineLineColor_load_le_ceilDiv_period
      alpha beta gamma K L c base step hK

/-- The generalized line-load bound with an explicit finite-grid domain
certificate. -/
theorem affineLineColor_finiteGrid_load_le
    (N alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (_hGrid : ∀ t < L, inGrid N (linePoint base step t)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step :=
  affineLineColor_load_le_ceilDiv_period
    alpha beta gamma K L c base step hK

/-- The old fixed-color index set is the {lit}`(1,M,0)` specialization. -/
theorem affineLineColorIndices_fixed_eq_lineColorIndices
    (M K L c : Nat) (base step : Nat × Nat) :
    affineLineColorIndices 1 M 0 K L c base step =
      lineColorIndices M K L c base step := by
  simp [affineLineColorIndices, lineColorIndices,
    affineGridColor_fixed_eq_affineChainColor]

end CLRS.Research.ThreeDIC

