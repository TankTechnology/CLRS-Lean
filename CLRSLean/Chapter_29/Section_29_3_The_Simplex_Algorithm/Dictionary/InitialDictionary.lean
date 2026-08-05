import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.BasicSolution
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

/-!
# 29.3 Initial dictionaries

This module converts a standard-form program into the initial CLRS dictionary:
original variables are nonbasic, slack variables are basic, and the dictionary
rows are exactly the slack equations from Section 29.1.

Main results:

- {lit}`initialDictionary_satisfies_iff`.
- {lit}`initialDictionary_satisfies_of_slackExtension`.
- {lit}`initialDictionary_objectiveRhs`.

Current gaps:

- A negative right-hand side can make the initial basic solution infeasible;
  Section 29.5's auxiliary LP will handle that case.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace StandardLP

/-- The initial slack-form dictionary of a standard-form program. -/
def initialDictionary (P : StandardLP m n) : Dictionary m n where
  labels := Equiv.sumComm (Fin m) (Fin n)
  b := P.b
  a := P.A
  v := 0
  c := P.c

/-- Combine original and slack vectors into one dictionary assignment. -/
def combinedAssignment (x : Fin n → ℝ) (s : Fin m → ℝ) : LPVar m n → ℝ
  | .inl j => x j
  | .inr i => s i

/-- The initial basic slots contain the slack variables. -/
@[simp] theorem initialDictionary_basicVar (P : StandardLP m n) (i : Fin m) :
    P.initialDictionary.basicVar i = Sum.inr i := by
  rfl

/-- The initial nonbasic slots contain the original variables. -/
@[simp] theorem initialDictionary_nonbasicVar (P : StandardLP m n) (j : Fin n) :
    P.initialDictionary.nonbasicVar j = Sum.inl j := by
  rfl

/-- A combined assignment is nonnegative exactly when both component vectors
are coordinatewise nonnegative. -/
theorem combinedAssignment_nonnegative_iff
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    Dictionary.IsNonnegativeAssignment (combinedAssignment x s) ↔
      IsNonnegative x ∧ IsNonnegative s := by
  constructor
  · intro h
    exact ⟨fun j => h (.inl j), fun i => h (.inr i)⟩
  · rintro ⟨hx, hs⟩ q
    cases q with
    | inl j => exact hx j
    | inr i => exact hs i

/-- The initial dictionary rows are exactly the standard slack equations. -/
theorem initialDictionary_satisfies_iff (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    P.initialDictionary.Satisfies (combinedAssignment x s) ↔
      ∀ i, (P.A *ᵥ x) i + s i = P.b i := by
  change (∀ i, s i = P.b i - ∑ j, P.A i j * x j) ↔
    ∀ i, (∑ j, P.A i j * x j) + s i = P.b i
  constructor <;> intro h i
  · have hi := h i
    linarith
  · have hi := h i
    linarith

/-- Every nonnegative slack extension satisfies the initial dictionary rows. -/
theorem initialDictionary_satisfies_of_slackExtension
    {P : StandardLP m n} {x : Fin n → ℝ} {s : Fin m → ℝ}
    (h : P.IsSlackExtension x s) :
    P.initialDictionary.Satisfies (combinedAssignment x s) :=
  (P.initialDictionary_satisfies_iff x s).2 h.2.2

/-- The initial dictionary objective is the original primal objective. -/
theorem initialDictionary_objectiveRhs (P : StandardLP m n)
    (x : Fin n → ℝ) (s : Fin m → ℝ) :
    P.initialDictionary.objectiveRhs (combinedAssignment x s) = P.objective x := by
  change 0 + (∑ j, P.c j * x j) = ∑ j, P.c j * x j
  simp

/-- The initial basic solution is feasible exactly when every original
right-hand side is nonnegative. -/
theorem initialDictionary_isBasicFeasible_iff (P : StandardLP m n) :
    P.initialDictionary.IsBasicFeasible ↔ ∀ i, 0 ≤ P.b i :=
  Iff.rfl

end StandardLP
end Chapter29
end CLRS
