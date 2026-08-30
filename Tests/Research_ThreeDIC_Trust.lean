import CLRSLean.Audit.Axioms
import CLRSLean.Research.ThreeDIC.AffineDirectionCodesign
import CLRSLean.Research.ThreeDIC.AffineFiniteConnectivity
import CLRSLean.Research.ThreeDIC.AffineStripTightness
import CLRSLean.Research.ThreeDIC.BalancedAffineCodesign
import CLRSLean.Research.ThreeDIC.LineDefectLoad
import CLRSLean.Research.ThreeDIC.StripDefectLoad
import CLRSLean.Research.ThreeDIC.WindowLoad

/-!
# Trust audit: 3D-IC affine route A

The eleven audited route A headline and affine-strip tightness declarations
may depend only on the repository's accepted Lean/Mathlib logical foundations
(`propext`, `Classical.choice`, and `Quot.sound`).
-/

#assert_axioms CLRS.Research.ThreeDIC.affineChainColor_finiteGrid_connected
#assert_axioms CLRS.Research.ThreeDIC.lineColor_load_le_ceilDiv_period
#assert_axioms CLRS.Research.ThreeDIC.affineChainColor_window_load_le_ceilDiv
#assert_axioms CLRS.Research.ThreeDIC.stripColor_load_le_phase_periods
#assert_axioms CLRS.Research.ThreeDIC.affineStripColor_load_le_phase_periods
#assert_axioms CLRS.Research.ThreeDIC.affineStripColor_load_le_familyScore
#assert_axioms CLRS.Research.ThreeDIC.exists_canonicalAffineCoefficients_minimizer
#assert_axioms CLRS.Research.ThreeDIC.affineGridColor_window_count_eq_of_coprime_coefficient
#assert_axioms CLRS.Research.ThreeDIC.exists_balancedAffineCoefficients_minimizer
#assert_axioms CLRS.Research.ThreeDIC.affineStripFundamentalColor_image_eq_range
#assert_axioms CLRS.Research.ThreeDIC.affineStripColor_load_eq_phase_periods
