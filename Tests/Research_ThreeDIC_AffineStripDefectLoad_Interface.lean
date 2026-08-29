import CLRSLean.Research.ThreeDIC.AffineStripDefectLoad

open CLRS.Research.ThreeDIC

#check affineStripColorPoints
#check affineStripAcrossPeriod
#check affineStripAcrossPeriod_pos
#check affineStripColor_load_le_phase_periods
#check affineStripColor_finiteGrid_load_le_phase_periods
#check affineStripColorPoints_fixed_eq_stripColorPoints
#check affineStripAcrossPeriod_fixed_eq_stripAcrossColorPeriod
#check affineStripAcrossPeriod_mod_coefficients

example
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along) :=
  affineStripColor_load_le_phase_periods
    alpha beta gamma K W L c base along across hK

example
    (N alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K)
    (hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along) :=
  affineStripColor_finiteGrid_load_le_phase_periods
    N alpha beta gamma K W L c base along across hK hGrid

example
    (M K W L c : Nat) (base along across : Nat × Nat) :
    affineStripColorPoints 1 M 0 K W L c base along across =
      stripColorPoints M K W L c base along across :=
  affineStripColorPoints_fixed_eq_stripColorPoints
    M K W L c base along across

example
    (M K : Nat) (along across : Nat × Nat) :
    affineStripAcrossPeriod 1 M K along across =
      stripAcrossColorPeriod M K along across :=
  affineStripAcrossPeriod_fixed_eq_stripAcrossColorPeriod
    M K along across

example : affineStripAcrossPeriod 1 2 8 (0, 1) (1, 0) = 2 := by decide

example
    (alpha beta K : Nat) (along across : Nat × Nat) :
    affineStripAcrossPeriod (alpha % K) (beta % K) K along across =
      affineStripAcrossPeriod alpha beta K along across :=
  affineStripAcrossPeriod_mod_coefficients alpha beta K along across

example :
    (affineStripColorPoints 2 1 4 7 2 5 4
      (0, 0) (1, 0) (0, 1)).card = 2 := by
  decide

example :
    (affineStripColorPoints 2 1 4 7 0 5 4
      (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (affineStripColorPoints 2 1 4 7 3 0 4
      (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (affineStripColorPoints 0 0 4 7 3 4 4
      (2, 5) (0, 0) (0, 0)).card = 1 := by
  decide
