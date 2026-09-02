import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Algebra

/-!
# 29.3 Minimum-ratio feasibility

The textbook minimum-ratio choice selects a leaving row whose positive pivot
coefficient gives the smallest bound on the entering variable.  If the old
dictionary is basic feasible, this condition makes every constant in the
pivoted dictionary nonnegative.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Row {lit}`l` realizes the textbook minimum-ratio test for entering column
{lit}`e`.
Only rows with a positive coefficient in that column constrain the ratio. -/
def IsMinimumRatio (D : Dictionary m n) (e : Fin n) (l : Fin m) : Prop :=
  0 < D.a l e ∧
    ∀ i, 0 < D.a i e → D.b l / D.a l e ≤ D.b i / D.a i e

namespace IsMinimumRatio

/-- A minimum-ratio row has a positive pivot coefficient. -/
theorem pivotCoefficient_pos {D : Dictionary m n} {e : Fin n} {l : Fin m}
    (h : D.IsMinimumRatio e l) : 0 < D.a l e :=
  h.1

/-- The chosen ratio is no larger than every other constraining ratio. -/
theorem ratio_le {D : Dictionary m n} {e : Fin n} {l : Fin m}
    (h : D.IsMinimumRatio e l) (i : Fin m) (hi : 0 < D.a i e) :
    D.b l / D.a l e ≤ D.b i / D.a i e :=
  h.2 i hi

end IsMinimumRatio

/-- Every constant produced by a minimum-ratio pivot is nonnegative. -/
theorem pivot_b_nonnegative (D : Dictionary m n) (e : Fin n) (l : Fin m)
    (hD : D.IsBasicFeasible) (hmin : D.IsMinimumRatio e l) (i : Fin m) :
    0 ≤ (D.pivot l e hmin.pivotCoefficient_pos.ne').b i := by
  by_cases hi : i = l
  · subst i
    rw [pivot_b_leaving]
    exact div_nonneg (hD l) hmin.pivotCoefficient_pos.le
  · rw [pivot_b_of_ne D l i e hmin.pivotCoefficient_pos.ne' hi]
    by_cases hie : 0 < D.a i e
    · have hratio := hmin.ratio_le i hie
      have hmul : D.b l / D.a l e * D.a i e ≤ D.b i :=
        (le_div_iff₀ hie).mp hratio
      nlinarith
    · have ha : D.a i e ≤ 0 := le_of_not_gt hie
      have hratio0 : 0 ≤ D.b l / D.a l e :=
        div_nonneg (hD l) hmin.pivotCoefficient_pos.le
      have hprod : D.a i e * (D.b l / D.a l e) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ha hratio0
      linarith [hD i]

/-- The textbook minimum-ratio PIVOT preserves basic feasibility. -/
theorem pivot_isBasicFeasible (D : Dictionary m n) (e : Fin n) (l : Fin m)
    (hD : D.IsBasicFeasible) (hmin : D.IsMinimumRatio e l) :
    (D.pivot l e hmin.pivotCoefficient_pos.ne').IsBasicFeasible :=
  D.pivot_b_nonnegative e l hD hmin

end Dictionary
end Chapter29
end CLRS
