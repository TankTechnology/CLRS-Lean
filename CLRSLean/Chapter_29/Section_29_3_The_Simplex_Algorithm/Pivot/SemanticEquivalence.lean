import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.SumLemmas

/-!
# 29.3 PIVOT semantic equivalence

PIVOT algebraically solves one dictionary row for the entering variable and
substitutes it into every other row and the objective.  Consequently it
represents exactly the same assignments and objective function.

Main results:

- {lit}`pivot_satisfies_iff`.
- {lit}`pivot_objectiveRhs_eq`.
-/

namespace CLRS
namespace Chapter29

open scoped BigOperators

namespace Dictionary

/-- Split an original row expression at the entering column. -/
theorem rowRhs_eq_split (D : Dictionary m n) (x : LPVar m n → ℝ)
    (i : Fin m) (e : Fin n) :
    D.rowRhs x i = D.b i -
      (D.a i e * x (D.nonbasicVar e) +
        sumExcept e (fun j => D.a i j * x (D.nonbasicVar j))) := by
  rw [rowRhs, sum_eq_term_add_sumExcept]

/-- The pivot-row coefficient sum in solved form. -/
theorem pivot_sum_leaving (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (∑ j, (D.pivot l e h).a l j *
      x ((D.pivot l e h).nonbasicVar j)) =
      (1 / D.a l e) * x (D.basicVar l) +
        sumExcept e (fun j =>
          (D.a l j / D.a l e) * x (D.nonbasicVar j)) := by
  rw [sum_eq_term_add_sumExcept]
  congr 1
  · rw [pivot_a_leaving_entering, pivot_nonbasicVar_entering]
  · apply Finset.sum_congr rfl
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [pivot_a_leaving_of_ne D l e j h hje,
      pivot_nonbasicVar_of_ne D l e j h hje]

/-- The solved pivot row written as a right-hand-side expression. -/
theorem pivot_rowRhs_leaving (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (D.pivot l e h).rowRhs x l =
      D.b l / D.a l e -
        ((1 / D.a l e) * x (D.basicVar l) +
          sumExcept e (fun j =>
            (D.a l j / D.a l e) * x (D.nonbasicVar j))) := by
  rw [rowRhs, pivot_b_leaving, pivot_sum_leaving]

/-- The old leaving-row equation is equivalent to the solved entering-variable
equation in the pivoted dictionary. -/
theorem pivot_leaving_equation_iff (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    x (D.basicVar l) = D.rowRhs x l ↔
      x ((D.pivot l e h).basicVar l) =
        (D.pivot l e h).rowRhs x l := by
  rw [pivot_basicVar_leaving, rowRhs_eq_split,
    pivot_rowRhs_leaving, sumExcept_div_mul]
  constructor
  · intro hold
    field_simp [h] at hold ⊢
    linarith
  · intro hnew
    field_simp [h] at hnew ⊢
    linarith

/-- The updated coefficient sum for a nonleaving row. -/
theorem pivot_sum_other (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l i : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (hi : i ≠ l) :
    (∑ j, (D.pivot l e h).a i j *
      x ((D.pivot l e h).nonbasicVar j)) =
      (-D.a i e * (1 / D.a l e)) * x (D.basicVar l) +
        sumExcept e (fun j =>
          (D.a i j - D.a i e * (D.a l j / D.a l e)) *
            x (D.nonbasicVar j)) := by
  rw [sum_eq_term_add_sumExcept]
  congr 1
  · rw [pivot_a_of_ne_entering D l i e h hi,
      pivot_nonbasicVar_entering]
  · apply Finset.sum_congr rfl
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [pivot_a_of_ne D l i e j h hi hje,
      pivot_nonbasicVar_of_ne D l e j h hje]

/-- For any other row, substituting the solved pivot row leaves its represented
right-hand side unchanged. -/
theorem pivot_rowRhs_other_eq (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l i : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (hi : i ≠ l)
    (hl : x (D.basicVar l) = D.rowRhs x l) :
    (D.pivot l e h).rowRhs x i = D.rowRhs x i := by
  rw [rowRhs_eq_split D x l e] at hl
  rw [rowRhs, pivot_b_of_ne D l i e h hi, pivot_sum_other D x l i e h hi,
    rowRhs_eq_split D x i e, sumExcept_pivot_update]
  have hmul := congrArg (fun t : ℝ => D.a i e * t) hl
  field_simp [h] at hmul ⊢
  ring_nf at hmul ⊢
  linarith

/-- PIVOT preserves exactly the set of assignments satisfying the dictionary
equations. -/
theorem pivot_satisfies_iff (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    D.Satisfies x ↔ (D.pivot l e h).Satisfies x := by
  constructor
  · intro hx i
    by_cases hi : i = l
    · subst i
      exact (D.pivot_leaving_equation_iff x l e h).1 (hx l)
    · rw [pivot_basicVar_of_ne D l i e h hi,
        pivot_rowRhs_other_eq D x l i e h hi (hx l)]
      exact hx i
  · intro hx i
    have holdLeaving : x (D.basicVar l) = D.rowRhs x l :=
      (D.pivot_leaving_equation_iff x l e h).2 (hx l)
    by_cases hi : i = l
    · simpa [hi] using holdLeaving
    · rw [← pivot_basicVar_of_ne D l i e h hi,
        ← pivot_rowRhs_other_eq D x l i e h hi holdLeaving]
      exact hx i

/-- The pivoted objective coefficient sum in terms of the old labels. -/
theorem pivot_objective_sum (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    (∑ j, (D.pivot l e h).c j *
      x ((D.pivot l e h).nonbasicVar j)) =
      (-D.c e * (1 / D.a l e)) * x (D.basicVar l) +
        sumExcept e (fun j =>
          (D.c j - D.c e * (D.a l j / D.a l e)) *
            x (D.nonbasicVar j)) := by
  rw [sum_eq_term_add_sumExcept]
  congr 1
  · rw [pivot_c_entering, pivot_nonbasicVar_entering]
  · apply Finset.sum_congr rfl
    intro j hj
    have hje : j ≠ e := (Finset.mem_erase.mp hj).1
    rw [pivot_c_of_ne D l e j h hje,
      pivot_nonbasicVar_of_ne D l e j h hje]

/-- On every represented assignment, PIVOT preserves the objective expression. -/
theorem pivot_objectiveRhs_eq (D : Dictionary m n)
    (x : LPVar m n → ℝ) (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0)
    (hx : D.Satisfies x) :
    (D.pivot l e h).objectiveRhs x = D.objectiveRhs x := by
  rw [objectiveRhs, pivot_v_apply, pivot_objective_sum, objectiveRhs,
    sum_eq_term_add_sumExcept e
      (fun j => D.c j * x (D.nonbasicVar j)),
    sumExcept_pivot_update]
  have hl := hx l
  rw [rowRhs_eq_split D x l e] at hl
  have hmul := congrArg (fun t : ℝ => D.c e * t) hl
  field_simp [h] at hmul ⊢
  ring_nf at hmul ⊢
  linarith

end Dictionary
end Chapter29
end CLRS
