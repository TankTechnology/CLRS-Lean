import CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.ComplementarySlackness
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Coefficients

/-!
# 29.3 Dual certificates from terminal dictionaries

When every reduced cost is nonpositive, the negated objective coefficients
of the original slack variables are the textbook dual variables.  Dictionary
equivalence proves both dual feasibility and equality of objective values.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace Dictionary

/-- Nonpositive reduced costs make the stable objective coefficient of every
variable nonpositive; basic variables have coefficient zero. -/
theorem objectiveCoeff_nonpos_of_reducedCosts (D : Dictionary m n)
    (hc : ∀ j, D.c j ≤ 0) (q : LPVar m n) :
    D.objectiveCoeff q ≤ 0 := by
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · simp
  · simpa using hc j

/-- The shadow-price vector read from a terminal dictionary. -/
def dualCertificate (D : Dictionary m n) : Fin m → ℝ :=
  fun i => -D.objectiveCoeff (.inr i)

/-- The shadow prices of a terminal dictionary form a feasible solution of
the dual of the original standard-form program. -/
theorem dualCertificate_isDualFeasible (P : StandardLP m n)
    (D : Dictionary m n) (hEq : P.initialDictionary.Equivalent D)
    (hc : ∀ j, D.c j ≤ 0) :
    P.IsDualFeasible D.dualCertificate := by
  constructor
  · intro i
    exact neg_nonneg.mpr
      (D.objectiveCoeff_nonpos_of_reducedCosts hc (.inr i))
  · intro j
    have hid := hEq.entering_coefficient_identity j
    have horiginal : D.objectiveCoeff (.inl j) ≤ 0 :=
      D.objectiveCoeff_nonpos_of_reducedCosts hc (.inl j)
    have hsum :
        (P.A.transpose *ᵥ D.dualCertificate) j =
          -(∑ i, D.objectiveCoeff (.inr i) * P.A i j) := by
      change (∑ i, P.A i j * (-D.objectiveCoeff (.inr i))) = _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    change P.c j = D.objectiveCoeff (.inl j) -
      ∑ i, D.objectiveCoeff (.inr i) * P.A i j at hid
    rw [hsum]
    linarith

/-- The objective of the terminal dual certificate equals the terminal
dictionary's objective constant. -/
theorem dualCertificate_objective_eq_v (P : StandardLP m n)
    (D : Dictionary m n) (hEq : P.initialDictionary.Equivalent D) :
    P.dualObjective D.dualCertificate = D.v := by
  let D₀ := P.initialDictionary
  have hobj := hEq.2 D₀.basicAssignment D₀.basicAssignment_satisfies
  have hsum :
      (∑ q, D.objectiveCoeff q * D₀.basicAssignment q) =
        ∑ i, D.objectiveCoeff (.inr i) * P.b i := by
    rw [D₀.sum_eq_sum_labels, Fintype.sum_sum_type]
    change
      (∑ i, D.objectiveCoeff (D₀.basicVar i) *
          D₀.basicAssignment (D₀.basicVar i)) +
        (∑ j, D.objectiveCoeff (D₀.nonbasicVar j) *
          D₀.basicAssignment (D₀.nonbasicVar j)) = _
    simp only [Dictionary.basicAssignment_basicVar,
      Dictionary.basicAssignment_nonbasicVar, mul_zero,
      Finset.sum_const_zero, add_zero]
    change (∑ i, D.objectiveCoeff (.inr i) * P.b i) = _
    rfl
  have hzero :
      0 = D.v + ∑ i, D.objectiveCoeff (.inr i) * P.b i := by
    calc
      0 = D₀.objectiveRhs D₀.basicAssignment := by
        rw [D₀.objectiveRhs_basicAssignment]
        rfl
      _ = D.objectiveRhs D₀.basicAssignment := hobj
      _ = D.v + ∑ q, D.objectiveCoeff q * D₀.basicAssignment q :=
        D.objectiveRhs_eq_fullSum D₀.basicAssignment
      _ = D.v + ∑ i, D.objectiveCoeff (.inr i) * P.b i := by
        rw [hsum]
  change (∑ i, P.b i * (-D.objectiveCoeff (.inr i))) = D.v
  have hneg :
      (∑ i, P.b i * (-D.objectiveCoeff (.inr i))) =
        -(∑ i, D.objectiveCoeff (.inr i) * P.b i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hneg]
  linarith

end Dictionary
end Chapter29
end CLRS
