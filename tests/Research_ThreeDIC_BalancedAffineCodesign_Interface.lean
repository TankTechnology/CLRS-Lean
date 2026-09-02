import CLRSLean.Research.ThreeDIC.BalancedAffineCodesign

/-!
# Research interface: balanced affine direction co-design

This file freezes the certified coefficient domain, its translated-window
admissibility theorem, and exact score minimization inside that domain.
-/

open CLRS.Research.ThreeDIC

#check balancedAffineCoefficientCandidates
#check mem_balancedAffineCoefficientCandidates_iff
#check balancedAffineCoefficientCandidates_nonempty
#check balancedAffineCoefficient_window_count_eq
#check exists_balancedAffineCoefficients_score_minimizer
#check exists_balancedAffineCoefficients_minimizer

example (K : Nat) (coeff : AffineCoefficients) :
    coeff ∈ balancedAffineCoefficientCandidates K ↔
      coeff.alpha < K ∧ coeff.beta < K ∧
        (Nat.Coprime K coeff.alpha ∨ Nat.Coprime K coeff.beta) :=
  mem_balancedAffineCoefficientCandidates_iff K coeff

example (K : Nat) (hK : 0 < K) :
    (balancedAffineCoefficientCandidates K).Nonempty :=
  balancedAffineCoefficientCandidates_nonempty K hK

example
    (K : Nat) (family : Finset StripDefectShape) (hK : 0 < K) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      ∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family :=
  exists_balancedAffineCoefficients_score_minimizer K family hK

example
    (M K gamma p q c : Nat) (coeff : AffineCoefficients)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcoeff : coeff ∈ balancedAffineCoefficientCandidates K) :
    affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
      (M * M) / K :=
  balancedAffineCoefficient_window_count_eq
    M K gamma p q c coeff hK hKM hc hcoeff

example
    (M K : Nat) (family : Finset StripDefectShape)
    (hK : 0 < K) (hKM : K ∣ M) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      (∀ gamma p q c, c < K →
        affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
          (M * M) / K) ∧
      (∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family) :=
  exists_balancedAffineCoefficients_minimizer M K family hK hKM

example :
    ({ alpha := 0, beta := 0 } : AffineCoefficients) ∈
      balancedAffineCoefficientCandidates 1 := by decide

example :
    ({ alpha := 1, beta := 2 } : AffineCoefficients) ∈
      balancedAffineCoefficientCandidates 6 := by decide

example :
    ({ alpha := 2, beta := 4 } : AffineCoefficients) ∉
      balancedAffineCoefficientCandidates 6 := by decide

example (K : Nat) (coeff : AffineCoefficients) :
    affineDefectFamilyScore K coeff ∅ = 0 := by
  simp [affineDefectFamilyScore]
