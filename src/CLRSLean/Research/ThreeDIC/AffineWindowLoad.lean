import CLRSLean.Research.ThreeDIC.AffineColoring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.CardIntervalMod

/-!
# Exact window load for a balanced affine coefficient family

For the coloring {lit}`(alpha*i + beta*j + gamma) mod K`, a coordinate
coefficient coprime to {lit}`K` permutes the residues along that coordinate.
When {lit}`K` divides the side length {lit}`M`, every translated
{lit}`M x M` window therefore contains every valid color exactly
{lit}`M^2/K` times.

The condition proved here is sufficient, not a classification of all affine
colorings with balanced translated windows.
-/

namespace CLRS.Research.ThreeDIC

/-- Number of physical bump offsets of color {lit}`c` in the translated full
{lit}`M x M` window based at {lit}`(p,q)`. -/
def affineWindowColorCount
    (M K alpha beta gamma p q c : Nat) : Nat :=
  (((Finset.range M).product (Finset.range M)).filter fun offset =>
    affineGridColor alpha beta gamma K
      (p + offset.1) (q + offset.2) = c).card

private theorem exists_affine_residue_preimage
    (K alpha base c : Nat) (hK : 0 < K) (hc : c < K)
    (hcop : Nat.Coprime K alpha) :
    ∃ d < K, (base + alpha * d) % K = c := by
  let f : Fin K → Fin K := fun d =>
    ⟨(base + alpha * d.1) % K, Nat.mod_lt _ hK⟩
  have hinjective : Function.Injective f := by
    intro x y hxy
    apply Fin.ext
    have hmod :
        base + alpha * x.1 ≡ base + alpha * y.1 [MOD K] := by
      exact congrArg Fin.val hxy
    have hmul : alpha * x.1 ≡ alpha * y.1 [MOD K] :=
      hmod.add_left_cancel' base
    exact (hmul.cancel_left_of_coprime hcop).eq_of_lt_of_lt x.2 y.2
  obtain ⟨d, hd⟩ :=
    Finite.surjective_of_injective hinjective ⟨c, hc⟩
  exact ⟨d.1, d.2, congrArg Fin.val hd⟩

private theorem affine_residue_eq_iff_modEq
    (K alpha base c d : Nat) (hcop : Nat.Coprime K alpha)
    (hcolor : (base + alpha * d) % K = c) (t : Nat) :
    (base + alpha * t) % K = c ↔ t ≡ d [MOD K] := by
  constructor
  · intro ht
    have hmod : base + alpha * t ≡ base + alpha * d [MOD K] :=
      ht.trans hcolor.symm
    exact (hmod.add_left_cancel' base).cancel_left_of_coprime hcop
  · intro htd
    calc
      (base + alpha * t) % K = (base + alpha * d) % K :=
        (htd.mul_left alpha).add_left base
      _ = c := hcolor

private theorem affine_residue_count_eq_div
    (n K alpha base c : Nat) (hK : 0 < K) (hKn : K ∣ n)
    (hc : c < K) (hcop : Nat.Coprime K alpha) :
    n.count (fun t => (base + alpha * t) % K = c) = n / K := by
  obtain ⟨d, _hd, hcolor⟩ :=
    exists_affine_residue_preimage K alpha base c hK hc hcop
  calc
    n.count (fun t => (base + alpha * t) % K = c) =
        n.count (fun t => t ≡ d [MOD K]) := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr_right fun _ht =>
        affine_residue_eq_iff_modEq K alpha base c d hcop hcolor t
    _ = n / K := by
      rw [Nat.count_modEq_card n hK d, Nat.mod_eq_zero_of_dvd hKn]
      simp

private theorem card_filter_product_eq_sum_right
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (pred : alpha × beta → Prop)
    [DecidablePred pred] :
    ((s.product t).filter pred).card =
      ∑ y ∈ t, (s.filter fun x => pred (x, y)).card := by
  rw [Finset.product_eq_sprod]
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Finset.sum_product_right]
  simp only [← Finset.sum_filter, ← Finset.card_eq_sum_ones]

private theorem card_filter_product_eq_sum_left
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (pred : alpha × beta → Prop)
    [DecidablePred pred] :
    ((s.product t).filter pred).card =
      ∑ x ∈ s, (t.filter fun y => pred (x, y)).card := by
  rw [Finset.product_eq_sprod]
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  rw [Finset.sum_product]
  simp only [← Finset.sum_filter, ← Finset.card_eq_sum_ones]

private theorem affineGridColor_offset_eq_rowProgression
    (K alpha beta gamma p q i j : Nat) :
    affineGridColor alpha beta gamma K (p + i) (q + j) =
      (alpha * p + beta * (q + j) + gamma + alpha * i) % K := by
  unfold affineGridColor
  congr 1
  ring

private theorem affineGridColor_offset_eq_columnProgression
    (K alpha beta gamma p q i j : Nat) :
    affineGridColor alpha beta gamma K (p + i) (q + j) =
      (alpha * (p + i) + beta * q + gamma + beta * j) % K := by
  unfold affineGridColor
  congr 1
  ring

/-- Exact load in every translated full window when the horizontal affine
coefficient is coprime to the color modulus. -/
theorem affineGridColor_window_count_eq_of_coprime_alpha
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K alpha) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K := by
  unfold affineWindowColorCount
  rw [card_filter_product_eq_sum_right]
  have hrow : ∀ j ∈ Finset.range M,
      ((Finset.range M).filter fun i =>
        affineGridColor alpha beta gamma K (p + i) (q + j) = c).card =
        M / K := by
    intro j _hj
    rw [← Nat.count_eq_card_filter_range]
    simp_rw [affineGridColor_offset_eq_rowProgression]
    exact affine_residue_count_eq_div M K alpha
      (alpha * p + beta * (q + j) + gamma) c hK hKM hc hcop
  rw [Finset.sum_const_nat hrow, Finset.card_range]
  exact (Nat.mul_div_assoc M hKM).symm

/-- Exact load in every translated full window when the vertical affine
coefficient is coprime to the color modulus. -/
theorem affineGridColor_window_count_eq_of_coprime_beta
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K := by
  unfold affineWindowColorCount
  rw [card_filter_product_eq_sum_left]
  have hcolumn : ∀ i ∈ Finset.range M,
      ((Finset.range M).filter fun j =>
        affineGridColor alpha beta gamma K (p + i) (q + j) = c).card =
        M / K := by
    intro i _hi
    rw [← Nat.count_eq_card_filter_range]
    simp_rw [affineGridColor_offset_eq_columnProgression]
    exact affine_residue_count_eq_div M K beta
      (alpha * (p + i) + beta * q + gamma) c hK hKM hc hcop
  rw [Finset.sum_const_nat hcolumn, Finset.card_range]
  exact (Nat.mul_div_assoc M hKM).symm

/-- A coprime coefficient in either coordinate is a sufficient certificate
for exact balance in every translated full window. -/
theorem affineGridColor_window_count_eq_of_coprime_coefficient
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hunit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K := by
  cases hunit with
  | inl halpha =>
      exact affineGridColor_window_count_eq_of_coprime_alpha
        M K alpha beta gamma p q c hK hKM hc halpha
  | inr hbeta =>
      exact affineGridColor_window_count_eq_of_coprime_beta
        M K alpha beta gamma p q c hK hKM hc hbeta

end CLRS.Research.ThreeDIC
