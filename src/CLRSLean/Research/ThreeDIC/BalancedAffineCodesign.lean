import CLRSLean.Research.ThreeDIC.AffineDirectionCodesign
import CLRSLean.Research.ThreeDIC.AffineWindowLoad

/-!
# Direction co-design over a certified balanced affine family

The canonical coefficient residue domain is filtered to pairs whose horizontal
or vertical coefficient is coprime to the color modulus.  When the modulus
divides the target-window side length, every pair in this finite family has
exact translated-window load.  The existing direction-sensitive strip score
therefore has an exact minimizer without leaving the certified family.

This is a sufficient feasible family.  It is not a classification of every
balanced affine coloring and the minimized quantity remains an upper
certificate rather than measured repair yield.
-/

namespace CLRS.Research.ThreeDIC

/-- Canonical coefficient residues with at least one coordinate coprime to the
color modulus. -/
def balancedAffineCoefficientCandidates
    (K : Nat) : Finset AffineCoefficients :=
  (canonicalAffineCoefficientCandidates K).filter fun coeff =>
    Nat.Coprime K coeff.alpha ∨ Nat.Coprime K coeff.beta

/-- Exact membership characterization of the certified balanced coefficient
domain. -/
theorem mem_balancedAffineCoefficientCandidates_iff
    (K : Nat) (coeff : AffineCoefficients) :
    coeff ∈ balancedAffineCoefficientCandidates K ↔
      coeff.alpha < K ∧ coeff.beta < K ∧
        (Nat.Coprime K coeff.alpha ∨ Nat.Coprime K coeff.beta) := by
  simp only [balancedAffineCoefficientCandidates, Finset.mem_filter]
  constructor
  · rintro ⟨hcanonical, hcop⟩
    unfold canonicalAffineCoefficientCandidates at hcanonical
    obtain ⟨ab, hab, habEq⟩ := Finset.mem_image.mp hcanonical
    have hrange := Finset.mem_product.mp hab
    subst coeff
    exact ⟨Finset.mem_range.mp hrange.1,
      Finset.mem_range.mp hrange.2, hcop⟩
  · rintro ⟨halpha, hbeta, hcop⟩
    refine ⟨?_, hcop⟩
    unfold canonicalAffineCoefficientCandidates
    apply Finset.mem_image.mpr
    exact ⟨(coeff.alpha, coeff.beta),
      Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr halpha, Finset.mem_range.mpr hbeta⟩,
      by cases coeff; rfl⟩

/-- Every positive color modulus admits a certified balanced coefficient
pair, including the singleton residue domain at {lit}`K = 1`. -/
theorem balancedAffineCoefficientCandidates_nonempty
    (K : Nat) (hK : 0 < K) :
    (balancedAffineCoefficientCandidates K).Nonempty := by
  cases K with
  | zero => omega
  | succ K =>
      cases K with
      | zero =>
          refine ⟨{ alpha := 0, beta := 0 }, ?_⟩
          exact (mem_balancedAffineCoefficientCandidates_iff 1 _).2 (by simp)
      | succ K =>
          refine ⟨{ alpha := 1, beta := 0 }, ?_⟩
          exact (mem_balancedAffineCoefficientCandidates_iff (K + 2) _).2
            (by simp)

/-- Every member of the certified candidate domain has exact load for every
valid color in every translated full window when {lit}`K` divides {lit}`M`. -/
theorem balancedAffineCoefficient_window_count_eq
    (M K gamma p q c : Nat) (coeff : AffineCoefficients)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcoeff : coeff ∈ balancedAffineCoefficientCandidates K) :
    affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
      (M * M) / K := by
  exact affineGridColor_window_count_eq_of_coprime_coefficient
    M K coeff.alpha coeff.beta gamma p q c hK hKM hc
      ((mem_balancedAffineCoefficientCandidates_iff K coeff).1 hcoeff).2.2

/-- The finite certified balanced domain contains an exact minimizer of the
direction-sensitive defect-family certificate. -/
theorem exists_balancedAffineCoefficients_score_minimizer
    (K : Nat) (family : Finset StripDefectShape) (hK : 0 < K) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      ∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family :=
  exists_affineCoefficients_minimizer K family
    (balancedAffineCoefficientCandidates K)
    (balancedAffineCoefficientCandidates_nonempty K hK)

/-- **Balanced affine co-design certificate.**

For a positive color modulus dividing the target-window side length, there is
a canonical affine coefficient pair that simultaneously has exact load for
every valid color in every translated full window and minimizes the existing
direction-sensitive strip certificate among all pairs in the certified
balanced family. -/
theorem exists_balancedAffineCoefficients_minimizer
    (M K : Nat) (family : Finset StripDefectShape)
    (hK : 0 < K) (hKM : K ∣ M) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      (∀ gamma p q c, c < K →
        affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
          (M * M) / K) ∧
      (∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family) := by
  obtain ⟨coeff, hcoeff, hmin⟩ :=
    exists_balancedAffineCoefficients_score_minimizer K family hK
  refine ⟨coeff, hcoeff, ?_, hmin⟩
  intro gamma p q c hc
  exact balancedAffineCoefficient_window_count_eq
    M K gamma p q c coeff hK hKM hc hcoeff

end CLRS.Research.ThreeDIC
