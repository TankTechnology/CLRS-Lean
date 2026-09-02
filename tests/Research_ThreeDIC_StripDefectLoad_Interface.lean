import CLRSLean.Research.ThreeDIC.StripDefectLoad

open CLRS.Research.ThreeDIC

#check stripPoint
#check stripLinePoints
#check stripPoints
#check stripColorPoints
#check stripAcrossColorPeriod
#check stripAcrossColorPeriod_pos
#check stripColor_load_le_sum_lines
#check stripColor_load_le_phase_periods
#check stripColor_horizontal_load_le
#check stripColor_vertical_load_le_phase
#check stripColor_finiteGrid_load_le_phase_periods

example
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      W * ((L + lineColorPeriod M K along - 1) /
        lineColorPeriod M K along) :=
  stripColor_load_le_sum_lines M K W L c base along across hK

example
    (M K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < stripAcrossColorPeriod M K along across :=
  stripAcrossColorPeriod_pos M K along across hK

example
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along) :=
  stripColor_load_le_phase_periods M K W L c base along across hK

example
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card ≤
      W * ((L + K - 1) / K) :=
  stripColor_horizontal_load_le M K W L c base hK

example
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card ≤
      ((W + Nat.gcd K M - 1) / Nat.gcd K M) *
        ((L + K / Nat.gcd K M - 1) / (K / Nat.gcd K M)) :=
  stripColor_vertical_load_le_phase M K W L c base hK

example
    (N M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along) :=
  stripColor_finiteGrid_load_le_phase_periods
    N M K W L c base along across hK hGrid

example : stripAcrossColorPeriod 2 8 (0, 1) (1, 0) = 2 := by decide
example : stripAcrossColorPeriod 3 8 (1, 0) (0, 1) = 1 := by decide

example :
    (stripColorPoints 3 8 2 0 3 (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (stripColorPoints 3 1 2 3 0 (0, 0) (1, 0) (0, 1)).card = 6 := by
  decide

example :
    (stripPoints 2 3 (0, 0) (1, 0) (1, 0)).card = 4 := by
  decide

example :
    (stripColorPoints 3 8 2 5 3 (0, 0) (1, 0) (0, 1)).card = 2 := by
  decide

example :
    (stripColorPoints 2 8 4 5 0 (0, 0) (0, 1) (1, 0)).card = 3 := by
  decide

example :
    (stripColorPoints 3 8 0 5 0 (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (stripColorPoints 3 8 3 4 0 (0, 0) (0, 0) (0, 0)).card = 1 := by
  decide
