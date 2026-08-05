import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.Definitions

/-!
# 29.3 Dictionary variable semantics

This module records the partition of every dictionary variable into exactly
one basic or nonbasic slot.  These facts support the basic solution and later
PIVOT label bookkeeping.

Main results:

- {lit}`labels_basic_ne_nonbasic`.
- {lit}`exists_basic_or_nonbasic`.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Pointwise nonnegativity for a complete original/slack assignment. -/
def IsNonnegativeAssignment (x : LPVar m n → ℝ) : Prop :=
  ∀ q, 0 ≤ x q

/-- A variable cannot occupy a basic and a nonbasic slot simultaneously. -/
theorem labels_basic_ne_nonbasic (D : Dictionary m n)
    (i : Fin m) (j : Fin n) : D.basicVar i ≠ D.nonbasicVar j := by
  intro h
  have hpos : (Sum.inl i : Fin m ⊕ Fin n) = Sum.inr j := D.labels.injective h
  cases hpos

/-- Every variable occupies either a basic row or a nonbasic column. -/
theorem exists_basic_or_nonbasic (D : Dictionary m n) (q : LPVar m n) :
    (∃ i, q = D.basicVar i) ∨ (∃ j, q = D.nonbasicVar j) := by
  obtain ⟨p, rfl⟩ := D.labels.surjective q
  cases p with
  | inl i => exact Or.inl ⟨i, rfl⟩
  | inr j => exact Or.inr ⟨j, rfl⟩

end Dictionary
end Chapter29
end CLRS
