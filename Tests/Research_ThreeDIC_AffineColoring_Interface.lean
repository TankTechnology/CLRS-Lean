import CLRSLean.Research.ThreeDIC.AffineColoring

open CLRS.Research.ThreeDIC

#check affineGridColor
#check affineDirectionStep
#check affineLinePeriod
#check affineLinePeriod_pos
#check affineGridColor_linePoint
#check affineGridColor_line_periodic
#check affineGridColor_line_index_congruent
#check affineGridColor_fixed_eq_affineChainColor
#check affineDirectionStep_fixed_eq_lineColorStep
#check affineLinePeriod_fixed_eq_lineColorPeriod

example
    (alpha beta gamma K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineGridColor alpha beta gamma K
        (linePoint base step t).1 (linePoint base step t).2 =
      (alpha * base.1 + beta * base.2 + gamma +
        affineDirectionStep alpha beta step * t) % K :=
  affineGridColor_linePoint alpha beta gamma K base step t

example
    (alpha beta gamma K : Nat) (base step : Nat × Nat) (t : Nat) :
    affineGridColor alpha beta gamma K
        (linePoint base step (t + affineLinePeriod alpha beta K step)).1
        (linePoint base step (t + affineLinePeriod alpha beta K step)).2 =
      affineGridColor alpha beta gamma K
        (linePoint base step t).1 (linePoint base step t).2 :=
  affineGridColor_line_periodic alpha beta gamma K base step t

example
    (alpha beta gamma K : Nat) (base step : Nat × Nat)
    (hK : 0 < K) {s t : Nat}
    (hColor :
      affineGridColor alpha beta gamma K
          (linePoint base step s).1 (linePoint base step s).2 =
        affineGridColor alpha beta gamma K
          (linePoint base step t).1 (linePoint base step t).2) :
    s % affineLinePeriod alpha beta K step =
      t % affineLinePeriod alpha beta K step :=
  affineGridColor_line_index_congruent
    alpha beta gamma K base step hK hColor

example (M K i j : Nat) :
    affineGridColor 1 M 0 K i j = affineChainColor M K i j :=
  affineGridColor_fixed_eq_affineChainColor M K i j

example : affineGridColor 1 3 0 8 2 3 = 3 := by decide
example : affineGridColor 2 1 4 7 3 5 = 1 := by decide
example : affineDirectionStep 2 1 (3, 4) = 10 := by decide
example : affineLinePeriod 2 1 8 (3, 4) = 4 := by decide

