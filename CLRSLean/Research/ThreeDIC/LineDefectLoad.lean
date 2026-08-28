import CLRSLean.Research.ThreeDIC.FiniteGrid
import CLRSLean.Research.ThreeDIC.LineDefect
import Mathlib.Algebra.Order.Floor.Div

/-!
# Per-chain load bounds for finite lattice-line defects

For a finite prefix of a lattice-line defect, this module counts the bump
indices assigned to one affine repair-chain color.  Equal-colored indices lie
in one residue class modulo the line-color period, so mapping an index to its
quotient by that period is injective.  This yields the explicit ceiling bound
{lit}`ceil(L / T)` for prefix length {lit}`L` and period {lit}`T`.

The result is deterministic and combinatorial.  A finite-grid corollary makes
the geometric domain assumption explicit, but no probabilistic defect or
physical routing model is introduced.
-/

namespace CLRS.Research.ThreeDIC

/-- Indices below {lit}`L` on a lattice line that receive color {lit}`c`. -/
def lineColorIndices
    (M K L c : Nat) (base step : Nat × Nat) : Finset Nat :=
  (Finset.range L).filter (fun t =>
    affineChainColor M K (linePoint base step t).1
      (linePoint base step t).2 = c)

private theorem quotient_lt_ceilDiv
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

private theorem card_le_ceilDiv_of_mod_eq
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
    exact quotient_lt_ceilDiv hT (Finset.mem_range.mp (hRange ht))
  simpa only [Finset.card_range] using Finset.card_le_card hImageRange

/-- A color appears at most {lit}`ceil(L / T)` times in a length-{lit}`L`
line prefix, where {lit}`T` is the exact affine line-color period. -/
theorem lineColor_load_le_ceilDiv_period
    (M K L c : Nat) (base step : Nat × Nat) (hK : 0 < K) :
    (lineColorIndices M K L c base step).card ≤
      (L + lineColorPeriod M K step - 1) /
        lineColorPeriod M K step := by
  apply card_le_ceilDiv_of_mod_eq
    (lineColorIndices M K L c base step)
    (lineColorPeriod_pos M K step hK)
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro s hs t ht
    exact lineColor_index_congruent M K base step hK
      ((Finset.mem_filter.mp hs).2.trans (Finset.mem_filter.mp ht).2.symm)

/-- Horizontal defects cycle through every color before repeating. -/
theorem lineColor_horizontal_load_le
    (M K L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (lineColorIndices M K L c base (1, 0)).card ≤
      (L + K - 1) / K := by
  simpa [lineColorPeriod, lineColorStep] using
    lineColor_load_le_ceilDiv_period M K L c base (1, 0) hK

/-- Vertical defects have period {lit}`K / gcd(K, M)`. -/
theorem lineColor_vertical_load_le
    (M K L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (lineColorIndices M K L c base (0, 1)).card ≤
      (L + K / Nat.gcd K M - 1) / (K / Nat.gcd K M) := by
  simpa [lineColorPeriod, lineColorStep] using
    lineColor_load_le_ceilDiv_period M K L c base (0, 1) hK

/-- If the line color step is coprime to {lit}`K`, every chain receives at
most {lit}`ceil(L / K)` defect points. -/
theorem lineColor_coprime_load_le
    (M K L c : Nat) (base step : Nat × Nat) (hK : 0 < K)
    (hCoprime : Nat.Coprime K (lineColorStep M step)) :
    (lineColorIndices M K L c base step).card ≤
      (L + K - 1) / K := by
  simpa [lineColorPeriod, hCoprime] using
    lineColor_load_le_ceilDiv_period M K L c base step hK

/-- The same load bound for a line prefix explicitly certified to remain
inside an {lit}`N x N` bump grid. -/
theorem lineColor_finiteGrid_load_le
    (N M K L c : Nat) (base step : Nat × Nat) (hK : 0 < K)
    (_hGrid : ∀ t < L, inGrid N (linePoint base step t)) :
    (lineColorIndices M K L c base step).card ≤
      (L + lineColorPeriod M K step - 1) /
        lineColorPeriod M K step :=
  lineColor_load_le_ceilDiv_period M K L c base step hK

end CLRS.Research.ThreeDIC
