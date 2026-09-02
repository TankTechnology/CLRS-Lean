import CLRSLean.Research.ThreeDIC.AffineStripDefectLoad
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Finite-family affine coefficient/direction co-design

This module packages the generalized strip theorem as an EDA-facing load
certificate.  A defect family score is the maximum certificate over an
explicit finite set of strip shapes.  Every nonempty finite coefficient
candidate set contains an exact minimizer of that score.

The minimization theorem is candidate-relative.  It does not characterize all
window-balanced affine colorings, establish tightness, or model routing,
spares, mux reachability, or repair success.
-/

namespace CLRS.Research.ThreeDIC

/-- The two affine coefficients that determine directional color periods.
The additive offset is omitted because it relabels colors without changing a
load certificate. -/
structure AffineCoefficients where
  alpha : Nat
  beta : Nat
deriving DecidableEq, Repr

/-- One finite parallel-strip defect geometry. -/
structure StripDefectShape where
  width : Nat
  length : Nat
  along : Nat × Nat
  across : Nat × Nat
deriving DecidableEq, Repr

/-- Closed-form phase-aware upper certificate for one strip shape. -/
def affineStripLoadCertificate
    (K : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) : Nat :=
  ((shape.width + affineStripAcrossPeriod coeff.alpha coeff.beta K
      shape.along shape.across - 1) /
        affineStripAcrossPeriod coeff.alpha coeff.beta K
          shape.along shape.across) *
    ((shape.length + affineLinePeriod coeff.alpha coeff.beta K
      shape.along - 1) /
        affineLinePeriod coeff.alpha coeff.beta K shape.along)

/-- Worst closed-form strip certificate over an explicit finite defect
family.  The empty family has score zero. -/
def affineDefectFamilyScore
    (K : Nat) (coeff : AffineCoefficients)
    (family : Finset StripDefectShape) : Nat :=
  family.sup (affineStripLoadCertificate K coeff)

/-- The closed-form shape certificate bounds the actual distinct-physical-
point load for every offset, base, and requested color. -/
theorem affineStripColor_load_le_certificate
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (base : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineStripLoadCertificate K coeff shape := by
  simpa [affineStripLoadCertificate] using
    affineStripColor_load_le_phase_periods
      coeff.alpha coeff.beta gamma K shape.width shape.length c
      base shape.along shape.across hK

/-- The family score simultaneously bounds the actual load for every listed
strip shape. -/
theorem affineStripColor_load_le_familyScore
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (family : Finset StripDefectShape)
    (base : Nat × Nat) (hK : 0 < K) (hshape : shape ∈ family) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineDefectFamilyScore K coeff family := by
  exact (affineStripColor_load_le_certificate
    K gamma c coeff shape base hK).trans (Finset.le_sup hshape)

/-- Every nonempty finite coefficient candidate set contains an exact
minimizer of the finite defect-family score. -/
theorem exists_affineCoefficients_minimizer
    (K : Nat) (family : Finset StripDefectShape)
    (candidates : Finset AffineCoefficients) (hne : candidates.Nonempty) :
    ∃ coeff ∈ candidates, ∀ other ∈ candidates,
      affineDefectFamilyScore K coeff family ≤
        affineDefectFamilyScore K other family :=
  candidates.exists_min_image
    (fun coeff => affineDefectFamilyScore K coeff family) hne

/-- Canonical representative of a coefficient pair modulo the color
modulus. -/
def canonicalAffineCoefficients
    (K : Nat) (coeff : AffineCoefficients) : AffineCoefficients where
  alpha := coeff.alpha % K
  beta := coeff.beta % K

/-- A one-shape certificate depends only on the coefficient residue pair. -/
theorem affineStripLoadCertificate_canonical
    (K : Nat) (coeff : AffineCoefficients) (shape : StripDefectShape) :
    affineStripLoadCertificate K (canonicalAffineCoefficients K coeff) shape =
      affineStripLoadCertificate K coeff shape := by
  simp [affineStripLoadCertificate, canonicalAffineCoefficients,
    affineStripAcrossPeriod_mod_coefficients,
    affineLinePeriod_mod_coefficients]

/-- A finite defect-family score depends only on the coefficient residue
pair. -/
theorem affineDefectFamilyScore_canonical
    (K : Nat) (coeff : AffineCoefficients)
    (family : Finset StripDefectShape) :
    affineDefectFamilyScore K (canonicalAffineCoefficients K coeff) family =
      affineDefectFamilyScore K coeff family := by
  unfold affineDefectFamilyScore
  apply Finset.sup_congr rfl
  intro shape _hshape
  exact affineStripLoadCertificate_canonical K coeff shape

/-- The complete finite residue domain for affine coefficient pairs. -/
def canonicalAffineCoefficientCandidates
    (K : Nat) : Finset AffineCoefficients :=
  ((Finset.range K).product (Finset.range K)).image (fun ab =>
    { alpha := ab.1, beta := ab.2 })

/-- A positive modulus gives a nonempty canonical coefficient domain. -/
theorem canonicalAffineCoefficientCandidates_nonempty
    (K : Nat) (hK : 0 < K) :
    (canonicalAffineCoefficientCandidates K).Nonempty := by
  refine ⟨{ alpha := 0, beta := 0 }, ?_⟩
  unfold canonicalAffineCoefficientCandidates
  apply Finset.mem_image.mpr
  exact ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hK, Finset.mem_range.mpr hK⟩, rfl⟩

/-- Every natural coefficient pair has its canonical representative in the
finite residue domain. -/
theorem canonicalAffineCoefficients_mem_candidates
    (K : Nat) (coeff : AffineCoefficients) (hK : 0 < K) :
    canonicalAffineCoefficients K coeff ∈
      canonicalAffineCoefficientCandidates K := by
  unfold canonicalAffineCoefficients canonicalAffineCoefficientCandidates
  apply Finset.mem_image.mpr
  exact ⟨(coeff.alpha % K, coeff.beta % K), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt coeff.alpha hK),
      Finset.mem_range.mpr (Nat.mod_lt coeff.beta hK)⟩, rfl⟩

/-- For a positive modulus, the finite canonical residue domain contains a
family-score minimizer no worse than every natural coefficient pair. -/
theorem exists_canonicalAffineCoefficients_minimizer
    (K : Nat) (family : Finset StripDefectShape) (hK : 0 < K) :
    ∃ coeff ∈ canonicalAffineCoefficientCandidates K,
      ∀ other : AffineCoefficients,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family := by
  obtain ⟨best, hbest, hmin⟩ :=
    exists_affineCoefficients_minimizer K family
      (canonicalAffineCoefficientCandidates K)
      (canonicalAffineCoefficientCandidates_nonempty K hK)
  refine ⟨best, hbest, fun other => ?_⟩
  calc
    affineDefectFamilyScore K best family ≤
        affineDefectFamilyScore K
          (canonicalAffineCoefficients K other) family :=
      hmin _ (canonicalAffineCoefficients_mem_candidates K other hK)
    _ = affineDefectFamilyScore K other family :=
      affineDefectFamilyScore_canonical K other family

end CLRS.Research.ThreeDIC
