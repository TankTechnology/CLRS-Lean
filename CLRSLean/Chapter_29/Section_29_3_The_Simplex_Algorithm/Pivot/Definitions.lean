import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary

/-!
# 29.3 PIVOT definitions

This module implements the coefficient transformation in CLRS PIVOT.  Matrix
slots remain fixed while the leaving basic variable and entering nonbasic
variable exchange their labels.

Main declarations:

- {lit}`pivotSwap`: the position-label exchange.
- {lit}`pivotRowB` and {lit}`pivotRowCoeff`: the solved pivot row.
- {lit}`pivot`: the complete textbook dictionary update.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Exchange leaving basic position {lit}`l` with entering nonbasic position
{lit}`e`. -/
def pivotSwap (l : Fin m) (e : Fin n) :
    (Fin m ⊕ Fin n) ≃ (Fin m ⊕ Fin n) :=
  Equiv.swap (.inl l) (.inr e)

/-- The constant of the solved pivot row. -/
noncomputable def pivotRowB (D : Dictionary m n) (l : Fin m) (e : Fin n) : ℝ :=
  D.b l / D.a l e

/-- A coefficient of the solved pivot row.

Column {lit}`e` becomes the column of the old leaving variable after the label
swap, so its coefficient is the reciprocal pivot coefficient. -/
noncomputable def pivotRowCoeff (D : Dictionary m n)
    (l : Fin m) (e j : Fin n) : ℝ :=
  if j = e then 1 / D.a l e else D.a l j / D.a l e

/-- The CLRS PIVOT transformation for leaving row {lit}`l` and entering column
{lit}`e`.  The pivot coefficient must be nonzero so the later semantic theorems
may clear its denominator. -/
noncomputable def pivot (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (_h : D.a l e ≠ 0) : Dictionary m n where
  labels := (pivotSwap l e).trans D.labels
  b := fun i =>
    if i = l then D.pivotRowB l e
    else D.b i - D.a i e * D.pivotRowB l e
  a := fun i j =>
    if i = l then D.pivotRowCoeff l e j
    else if j = e then -D.a i e * D.pivotRowCoeff l e e
    else D.a i j - D.a i e * D.pivotRowCoeff l e j
  v := D.v + D.c e * D.pivotRowB l e
  c := fun j =>
    if j = e then -D.c e * D.pivotRowCoeff l e e
    else D.c j - D.c e * D.pivotRowCoeff l e j

end Dictionary
end Chapter29
end CLRS
