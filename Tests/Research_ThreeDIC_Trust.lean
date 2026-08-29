import CLRSLean.Audit.Axioms
import CLRSLean.Research.ThreeDIC.AffineFiniteConnectivity
import CLRSLean.Research.ThreeDIC.LineDefectLoad
import CLRSLean.Research.ThreeDIC.StripDefectLoad
import CLRSLean.Research.ThreeDIC.WindowLoad

/-!
# Trust audit: 3D-IC affine route A

The four route A headline theorems may depend only on the repository's accepted
Lean/Mathlib logical foundations (`propext`, `Classical.choice`, and
`Quot.sound`).
-/

#assert_axioms CLRS.Research.ThreeDIC.affineChainColor_finiteGrid_connected
#assert_axioms CLRS.Research.ThreeDIC.lineColor_load_le_ceilDiv_period
#assert_axioms CLRS.Research.ThreeDIC.affineChainColor_window_load_le_ceilDiv
#assert_axioms CLRS.Research.ThreeDIC.stripColor_load_le_phase_periods
