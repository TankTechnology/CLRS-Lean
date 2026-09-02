import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Feasibility

/-!
# 29.3 Objective progress after PIVOT

For a positive reduced-cost entering variable, the minimum-ratio pivot never
decreases the objective value of the associated basic solution.  It increases
the value strictly when the leaving basic value is positive.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- The constant term of the objective after a PIVOT. -/
theorem pivot_v_eq (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) :
    (D.pivot l e h).v = D.v + D.c e * (D.b l / D.a l e) :=
  rfl

/-- A feasible minimum-ratio pivot on a positive reduced cost does not
decrease the basic objective value. -/
theorem pivot_v_mono (D : Dictionary m n) (hD : D.IsBasicFeasible)
    (hc : 0 < D.c e) (hmin : D.IsMinimumRatio e l) :
    D.v ≤ (D.pivot l e hmin.pivotCoefficient_pos.ne').v := by
  rw [pivot_v_eq]
  have hratio : 0 ≤ D.b l / D.a l e :=
    div_nonneg (hD l) hmin.pivotCoefficient_pos.le
  exact le_add_of_nonneg_right (mul_nonneg hc.le hratio)

/-- If the leaving basic value is positive, a positive-reduced-cost pivot
strictly increases the basic objective value. -/
theorem pivot_v_strict (D : Dictionary m n) (hc : 0 < D.c e)
    (hbl : 0 < D.b l) (hmin : D.IsMinimumRatio e l) :
    D.v < (D.pivot l e hmin.pivotCoefficient_pos.ne').v := by
  rw [pivot_v_eq]
  exact lt_add_of_pos_right D.v
    (mul_pos hc (div_pos hbl hmin.pivotCoefficient_pos))

end Dictionary
end Chapter29
end CLRS
