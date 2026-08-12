import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Trace

/-!
# 29.3 Objective coefficients across dictionaries

The textbook anti-cycling argument compares the coefficient of every stable
original/slack variable, assigning coefficient zero to basic variables.  The
main identity follows by evaluating two equivalent objectives on an entering
ray at parameters zero and one.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- Objective coefficient of a stable variable identity, with basic-variable
coefficients extended by zero. -/
def objectiveCoeff (D : Dictionary m n) (q : LPVar m n) : ℝ :=
  match D.labels.symm q with
  | .inl _ => 0
  | .inr j => D.c j

@[simp] theorem objectiveCoeff_basicVar (D : Dictionary m n) (i : Fin m) :
    D.objectiveCoeff (D.basicVar i) = 0 := by
  simp [objectiveCoeff, basicVar]

@[simp] theorem objectiveCoeff_nonbasicVar (D : Dictionary m n) (j : Fin n) :
    D.objectiveCoeff (D.nonbasicVar j) = D.c j := by
  simp [objectiveCoeff, nonbasicVar]

/-- Reindex a sum over stable variables by a dictionary's labeled slots. -/
theorem sum_eq_sum_labels (D : Dictionary m n) (f : LPVar m n → ℝ) :
    (∑ q, f q) = ∑ p : Fin m ⊕ Fin n, f (D.labels p) := by
  symm
  exact Fintype.sum_equiv D.labels _ _ (fun _ => rfl)

/-- The objective expression as a sum over every stable variable identity. -/
theorem objectiveRhs_eq_fullSum (D : Dictionary m n)
    (x : LPVar m n → ℝ) :
    D.objectiveRhs x = D.v + ∑ q, D.objectiveCoeff q * x q := by
  rw [objectiveRhs, D.sum_eq_sum_labels]
  rw [Fintype.sum_sum_type]
  simp [objectiveCoeff, nonbasicVar]

/-- Re-express one dictionary's objective on another dictionary's entering
ray.  Only the entering variable and the first dictionary's basic variables
can be nonzero. -/
theorem objectiveRhs_enteringRay_as_coeff (D E : Dictionary m n)
    (e : Fin n) (t : ℝ) :
    E.objectiveRhs (D.enteringRay e t) =
      E.v + E.objectiveCoeff (D.nonbasicVar e) * t +
        ∑ i, E.objectiveCoeff (D.basicVar i) *
          (D.b i - D.a i e * t) := by
  rw [E.objectiveRhs_eq_fullSum, D.sum_eq_sum_labels,
    Fintype.sum_sum_type]
  change E.v +
      ((∑ i, E.objectiveCoeff (D.basicVar i) *
          D.enteringRay e t (D.basicVar i)) +
        ∑ j, E.objectiveCoeff (D.nonbasicVar j) *
          D.enteringRay e t (D.nonbasicVar j)) = _
  simp_rw [D.enteringRay_basicVar]
  rw [sum_eq_term_add_sumExcept e, D.enteringRay_nonbasicVar_same]
  have hzero : sumExcept e (fun j =>
      E.objectiveCoeff (D.nonbasicVar j) *
        D.enteringRay e t (D.nonbasicVar j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [D.enteringRay_nonbasicVar_of_ne e t j hje, mul_zero]
  rw [hzero, add_zero]
  ring

namespace Equivalent

/-- Textbook coefficient-comparison identity (Equation 3.9 in the standard
Bland-rule proof). -/
theorem entering_coefficient_identity {D E : Dictionary m n}
    (h : D.Equivalent E) (e : Fin n) :
    D.c e = E.objectiveCoeff (D.nonbasicVar e) -
      ∑ i, E.objectiveCoeff (D.basicVar i) * D.a i e := by
  have hzero := h.2 (D.enteringRay e 0) (D.enteringRay_satisfies e 0)
  have hone := h.2 (D.enteringRay e 1) (D.enteringRay_satisfies e 1)
  rw [D.enteringRay_objectiveRhs,
    D.objectiveRhs_enteringRay_as_coeff E e 0] at hzero
  rw [D.enteringRay_objectiveRhs,
    D.objectiveRhs_enteringRay_as_coeff E e 1] at hone
  simp only [mul_zero, add_zero, sub_zero] at hzero
  simp only [mul_one] at hone
  have hsum :
      (∑ i, E.objectiveCoeff (D.basicVar i) *
          (D.b i - D.a i e)) =
        (∑ i, E.objectiveCoeff (D.basicVar i) * D.b i) -
          ∑ i, E.objectiveCoeff (D.basicVar i) * D.a i e := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum] at hone
  linarith

end Equivalent

/-- A nonzero objective coefficient identifies a nonbasic variable. -/
theorem not_mem_basicVariables_of_objectiveCoeff_ne_zero
    (D : Dictionary m n) {q : LPVar m n} (hq : D.objectiveCoeff q ≠ 0) :
    q ∉ D.basicVariables := by
  intro hmem
  obtain ⟨i, hi⟩ := (D.mem_basicVariables q).1 hmem
  rw [← hi, D.objectiveCoeff_basicVar] at hq
  exact hq rfl

/-- Bland entering minimality makes every lower-index stable variable's
objective coefficient nonpositive. -/
theorem IsBlandEntering.objectiveCoeff_nonpos_of_index_lt
    {D : Dictionary m n} {e : Fin n} (he : D.IsBlandEntering e)
    {q : LPVar m n}
    (hlt : variableIndex q < D.nonbasicVariableIndex e) :
    D.objectiveCoeff q ≤ 0 := by
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp
  · rw [D.objectiveCoeff_nonbasicVar]
    by_contra hnot
    have hpos : 0 < D.c j := lt_of_not_ge hnot
    have hmin := he.2 j hpos
    exact (not_lt_of_ge hmin) hlt

/-- A positive left side and nonpositive leading coefficient in the textbook
identity force some negative coefficient-row product. -/
theorem exists_negative_coefficient_product (D E : Dictionary m n)
    (e : Fin n) (hidentity :
      D.c e = E.objectiveCoeff (D.nonbasicVar e) -
        ∑ i, E.objectiveCoeff (D.basicVar i) * D.a i e)
    (hpositive : 0 < D.c e)
    (hleading : E.objectiveCoeff (D.nonbasicVar e) ≤ 0) :
    ∃ i, E.objectiveCoeff (D.basicVar i) * D.a i e < 0 := by
  have hsum : (∑ i, E.objectiveCoeff (D.basicVar i) * D.a i e) < 0 := by
    linarith
  by_contra hnone
  push Not at hnone
  have hnonneg : 0 ≤ ∑ i, E.objectiveCoeff (D.basicVar i) * D.a i e :=
    Finset.sum_nonneg fun i _ => hnone i
  exact (not_lt_of_ge hnonneg) hsum

end Dictionary
end Chapter29
end CLRS
