import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Definitions

/-!
# 29.3 PIVOT formula interface

These projection theorems expose each branch of the textbook update without
forcing later proofs to simplify nested conditionals.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- The entering variable occupies the leaving basic row after PIVOT. -/
@[simp] theorem pivot_basicVar_leaving (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).basicVar l = D.nonbasicVar e := by
  simp [pivot, basicVar, nonbasicVar, pivotSwap]

/-- The leaving variable occupies the entering nonbasic column after PIVOT. -/
@[simp] theorem pivot_nonbasicVar_entering (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).nonbasicVar e = D.basicVar l := by
  simp [pivot, basicVar, nonbasicVar, pivotSwap]

/-- Every other basic row keeps its variable label. -/
theorem pivot_basicVar_of_ne (D : Dictionary m n)
    (l i : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (hi : i ≠ l) :
    (D.pivot l e h).basicVar i = D.basicVar i := by
  change D.labels (pivotSwap l e (.inl i)) = D.labels (.inl i)
  rw [pivotSwap, Equiv.swap_apply_of_ne_of_ne]
  · simpa using hi
  · simp

/-- Every other nonbasic column keeps its variable label. -/
theorem pivot_nonbasicVar_of_ne (D : Dictionary m n)
    (l : Fin m) (e j : Fin n) (h : D.a l e ≠ 0) (hj : j ≠ e) :
    (D.pivot l e h).nonbasicVar j = D.nonbasicVar j := by
  change D.labels (pivotSwap l e (.inr j)) = D.labels (.inr j)
  rw [pivotSwap, Equiv.swap_apply_of_ne_of_ne]
  · simp
  · simpa using hj

/-- The new leaving-row constant is the minimum-ratio candidate. -/
@[simp] theorem pivot_b_leaving (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).b l = D.b l / D.a l e := by
  simp [pivot, pivotRowB]

/-- Every other row substitutes the solved entering variable. -/
theorem pivot_b_of_ne (D : Dictionary m n)
    (l i : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (hi : i ≠ l) :
    (D.pivot l e h).b i = D.b i - D.a i e * (D.b l / D.a l e) := by
  simp [pivot, pivotRowB, hi]

/-- The pivot row's entering-column coefficient is the reciprocal pivot. -/
@[simp] theorem pivot_a_leaving_entering (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).a l e = 1 / D.a l e := by
  simp [pivot, pivotRowCoeff]

/-- Other pivot-row coefficients are divided by the pivot coefficient. -/
theorem pivot_a_leaving_of_ne (D : Dictionary m n)
    (l : Fin m) (e j : Fin n) (h : D.a l e ≠ 0) (hj : j ≠ e) :
    (D.pivot l e h).a l j = D.a l j / D.a l e := by
  simp [pivot, pivotRowCoeff, hj]

/-- In another row, the entering column becomes the old leaving-variable
coefficient. -/
theorem pivot_a_of_ne_entering (D : Dictionary m n)
    (l i : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (hi : i ≠ l) :
    (D.pivot l e h).a i e = -D.a i e * (1 / D.a l e) := by
  simp [pivot, pivotRowCoeff, hi]

/-- Every nonpivot matrix entry receives the textbook substitution update. -/
theorem pivot_a_of_ne (D : Dictionary m n)
    (l i : Fin m) (e j : Fin n) (h : D.a l e ≠ 0)
    (hi : i ≠ l) (hj : j ≠ e) :
    (D.pivot l e h).a i j =
      D.a i j - D.a i e * (D.a l j / D.a l e) := by
  simp [pivot, pivotRowCoeff, hi, hj]

/-- PIVOT updates the objective constant by the entering coefficient times the
pivot-row constant. -/
@[simp] theorem pivot_v_apply (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).v = D.v + D.c e * (D.b l / D.a l e) := by
  rfl

/-- The entering column receives the old leaving variable's objective
coefficient. -/
@[simp] theorem pivot_c_entering (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).c e = -D.c e * (1 / D.a l e) := by
  simp [pivot, pivotRowCoeff]

/-- Every other objective coefficient receives the textbook substitution
update. -/
theorem pivot_c_of_ne (D : Dictionary m n)
    (l : Fin m) (e j : Fin n) (h : D.a l e ≠ 0) (hj : j ≠ e) :
    (D.pivot l e h).c j = D.c j - D.c e * (D.a l j / D.a l e) := by
  simp [pivot, pivotRowCoeff, hj]

end Dictionary
end Chapter29
end CLRS
