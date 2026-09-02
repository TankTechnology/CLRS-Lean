import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.Semantics

/-!
# 29.3 Basic solutions of dictionaries

The basic assignment sets every nonbasic variable to zero and reads each
basic variable from its row constant.  It automatically satisfies the
dictionary equations; it is nonnegative exactly when all row constants are.

Main results:

- {lit}`basicAssignment_satisfies`.
- {lit}`basicAssignment_nonnegative_iff`.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- The basic assignment: basic variables receive their row constants and
nonbasic variables receive zero. -/
def basicAssignment (D : Dictionary m n) : LPVar m n → ℝ := fun q =>
  match D.labels.symm q with
  | .inl i => D.b i
  | .inr _ => 0

/-- The basic assignment reads the constant from each basic row. -/
@[simp] theorem basicAssignment_basicVar (D : Dictionary m n) (i : Fin m) :
    D.basicAssignment (D.basicVar i) = D.b i := by
  simp [basicAssignment, basicVar]

/-- Every nonbasic variable is zero in the basic assignment. -/
@[simp] theorem basicAssignment_nonbasicVar (D : Dictionary m n) (j : Fin n) :
    D.basicAssignment (D.nonbasicVar j) = 0 := by
  simp [basicAssignment, nonbasicVar]

/-- The basic assignment satisfies all dictionary equations. -/
theorem basicAssignment_satisfies (D : Dictionary m n) :
    D.Satisfies D.basicAssignment := by
  intro i
  simp [rowRhs]

/-- The basic assignment is pointwise nonnegative exactly when the dictionary
has nonnegative basic right-hand sides. -/
theorem basicAssignment_nonnegative_iff (D : Dictionary m n) :
    IsNonnegativeAssignment D.basicAssignment ↔ D.IsBasicFeasible := by
  constructor
  · intro h i
    simpa using h (D.basicVar i)
  · intro h q
    rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simpa using h i
    · simp

end Dictionary
end Chapter29
end CLRS
