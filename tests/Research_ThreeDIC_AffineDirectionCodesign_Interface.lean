import CLRSLean.Research.ThreeDIC.AffineDirectionCodesign

open CLRS.Research.ThreeDIC

#check AffineCoefficients
#check StripDefectShape
#check affineStripLoadCertificate
#check affineDefectFamilyScore
#check affineStripColor_load_le_certificate
#check affineStripColor_load_le_familyScore
#check exists_affineCoefficients_minimizer
#check canonicalAffineCoefficients
#check affineStripLoadCertificate_canonical
#check affineDefectFamilyScore_canonical
#check canonicalAffineCoefficientCandidates
#check canonicalAffineCoefficientCandidates_nonempty
#check canonicalAffineCoefficients_mem_candidates
#check exists_canonicalAffineCoefficients_minimizer

example
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (base : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineStripLoadCertificate K coeff shape :=
  affineStripColor_load_le_certificate K gamma c coeff shape base hK

example
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (family : Finset StripDefectShape)
    (base : Nat × Nat) (hK : 0 < K) (hshape : shape ∈ family) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineDefectFamilyScore K coeff family :=
  affineStripColor_load_le_familyScore
    K gamma c coeff shape family base hK hshape

example
    (K : Nat) (family : Finset StripDefectShape)
    (candidates : Finset AffineCoefficients) (hne : candidates.Nonempty) :
    ∃ coeff ∈ candidates, ∀ other ∈ candidates,
      affineDefectFamilyScore K coeff family ≤
        affineDefectFamilyScore K other family :=
  exists_affineCoefficients_minimizer K family candidates hne

private def horizontalStrip : StripDefectShape where
  width := 2
  length := 5
  along := (1, 0)
  across := (0, 1)

private def verticalStrip : StripDefectShape where
  width := 4
  length := 5
  along := (0, 1)
  across := (1, 0)

private def coeffFastHorizontal : AffineCoefficients where
  alpha := 1
  beta := 2

private def coeffSlowHorizontal : AffineCoefficients where
  alpha := 2
  beta := 0

example :
    affineDefectFamilyScore 8 coeffFastHorizontal ∅ = 0 := by
  decide

example :
    affineStripLoadCertificate 8 coeffFastHorizontal horizontalStrip = 2 := by
  decide

example :
    affineDefectFamilyScore 8 coeffFastHorizontal {horizontalStrip} = 2 := by
  decide

example :
    affineDefectFamilyScore 8 coeffSlowHorizontal {horizontalStrip} = 4 := by
  decide

example :
    affineStripLoadCertificate 8 coeffFastHorizontal verticalStrip = 4 := by
  decide

example :
    ∃ coeff ∈ ({coeffFastHorizontal, coeffSlowHorizontal} :
        Finset AffineCoefficients),
      ∀ other ∈ ({coeffFastHorizontal, coeffSlowHorizontal} :
          Finset AffineCoefficients),
        affineDefectFamilyScore 8 coeff {horizontalStrip} ≤
          affineDefectFamilyScore 8 other {horizontalStrip} :=
  exists_affineCoefficients_minimizer 8 {horizontalStrip}
    {coeffFastHorizontal, coeffSlowHorizontal} (by simp)

example (K : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) :
    affineStripLoadCertificate K (canonicalAffineCoefficients K coeff) shape =
      affineStripLoadCertificate K coeff shape :=
  affineStripLoadCertificate_canonical K coeff shape

example (K : Nat) (coeff : AffineCoefficients)
    (family : Finset StripDefectShape) :
    affineDefectFamilyScore K (canonicalAffineCoefficients K coeff) family =
      affineDefectFamilyScore K coeff family :=
  affineDefectFamilyScore_canonical K coeff family

example (K : Nat) (hK : 0 < K) :
    (canonicalAffineCoefficientCandidates K).Nonempty :=
  canonicalAffineCoefficientCandidates_nonempty K hK

example (K : Nat) (family : Finset StripDefectShape) (hK : 0 < K) :
    ∃ coeff ∈ canonicalAffineCoefficientCandidates K,
      ∀ other : AffineCoefficients,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family :=
  exists_canonicalAffineCoefficients_minimizer K family hK

example :
    canonicalAffineCoefficients 8
      { alpha := 17, beta := 10 } = { alpha := 1, beta := 2 } := by
  decide
