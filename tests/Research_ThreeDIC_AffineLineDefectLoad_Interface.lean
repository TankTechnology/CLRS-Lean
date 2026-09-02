import CLRSLean.Research.ThreeDIC.AffineLineDefectLoad

open CLRS.Research.ThreeDIC

#check affineLineColorIndices
#check affineLineColor_load_le_ceilDiv_period
#check affineLineColor_coprime_load_le
#check affineLineColor_finiteGrid_load_le
#check affineLineColorIndices_fixed_eq_lineColorIndices

example
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step :=
  affineLineColor_load_le_ceilDiv_period
    alpha beta gamma K L c base step hK

example
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (hCoprime : Nat.Coprime K (affineDirectionStep alpha beta step)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + K - 1) / K :=
  affineLineColor_coprime_load_le
    alpha beta gamma K L c base step hK hCoprime

example
    (N alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (hGrid : ∀ t < L, inGrid N (linePoint base step t)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step :=
  affineLineColor_finiteGrid_load_le
    N alpha beta gamma K L c base step hK hGrid

example (M K L c : Nat) (base step : Nat × Nat) :
    affineLineColorIndices 1 M 0 K L c base step =
      lineColorIndices M K L c base step :=
  affineLineColorIndices_fixed_eq_lineColorIndices M K L c base step

example :
    (affineLineColorIndices 2 1 4 7 8 4 (0, 0) (3, 4)).card = 2 := by
  decide

example :
    (affineLineColorIndices 2 1 4 7 0 1 (0, 0) (3, 4)).card = 0 := by
  decide

example :
    (affineLineColorIndices 2 1 4 7 8 9 (0, 0) (3, 4)).card = 0 := by
  decide

example :
    (affineLineColorIndices 0 0 4 7 8 4 (2, 5) (0, 0)).card = 8 := by
  decide
