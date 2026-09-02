import CLRSLean.Research.ThreeDIC.WindowDiversity

/-!
# Research interface: affine repair-chain coloring

This interface test keeps the 3D-IC research baseline separate from the CLRS
textbook completion surface.  It records the intended deterministic coloring
and the theorem that every target-size window contains every repair chain.
-/

open CLRS.Research.ThreeDIC

#check affineChainColor
#check affineChainColor_lt
#check affineChainColor_window_surjective

example : affineChainColor 3 8 4 2 = 2 := by decide
