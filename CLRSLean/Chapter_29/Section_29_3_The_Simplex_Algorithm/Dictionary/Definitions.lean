import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms

/-!
# 29.3 Slack-form dictionaries

This module defines the fixed-slot dictionary representation used by the
Chapter 29 SIMPLEX development.  Basic and nonbasic slots keep fixed matrix
dimensions while an equivalence records which original or slack variable
currently occupies each slot.

Main declarations:

- {lit}`LPVar`: original and slack variable names.
- {lit}`Dictionary`: CLRS slack-form coefficients and variable labels.
- {lit}`Dictionary.Satisfies`: the represented row equations.
- {lit}`Dictionary.IsBasicFeasible`: nonnegative basic right-hand sides.

Downstream layers:

- Basic solutions, initial dictionaries, and PIVOT are proved in later modules.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

/-- Variable names for an LP with {lit}`n` original variables and {lit}`m`
slack variables. -/
abbrev LPVar (m n : ℕ) := Fin n ⊕ Fin m

/-- A CLRS slack-form dictionary with fixed basic/nonbasic slots.

The equivalence {lit}`labels` carries stable variable identities across pivots;
the matrices remain indexed by the fixed row and column slots. -/
structure Dictionary (m n : ℕ) where
  /-- Variable occupying each basic ({lit}`inl`) or nonbasic ({lit}`inr`) slot. -/
  labels : (Fin m ⊕ Fin n) ≃ LPVar m n
  /-- Constant term for each basic row. -/
  b : Fin m → ℝ
  /-- Row coefficients in {lit}`x_B = b - A x_N`. -/
  a : Matrix (Fin m) (Fin n) ℝ
  /-- Constant term of the objective expression. -/
  v : ℝ
  /-- Coefficients in {lit}`z = v + cᵀx_N`. -/
  c : Fin n → ℝ

namespace Dictionary

/-- The variable occupying basic row {lit}`i`. -/
def basicVar (D : Dictionary m n) (i : Fin m) : LPVar m n :=
  D.labels (.inl i)

/-- The variable occupying nonbasic column {lit}`j`. -/
def nonbasicVar (D : Dictionary m n) (j : Fin n) : LPVar m n :=
  D.labels (.inr j)

/-- The right-hand side {lit}`bᵢ - Σⱼ aᵢⱼxⱼ` of one dictionary row. -/
def rowRhs (D : Dictionary m n) (x : LPVar m n → ℝ) (i : Fin m) : ℝ :=
  D.b i - ∑ j, D.a i j * x (D.nonbasicVar j)

/-- The objective expression {lit}`v + Σⱼ cⱼxⱼ` represented by a dictionary. -/
def objectiveRhs (D : Dictionary m n) (x : LPVar m n → ℝ) : ℝ :=
  D.v + ∑ j, D.c j * x (D.nonbasicVar j)

/-- A complete assignment satisfies a dictionary when every basic variable
equals its represented row expression. -/
def Satisfies (D : Dictionary m n) (x : LPVar m n → ℝ) : Prop :=
  ∀ i, x (D.basicVar i) = D.rowRhs x i

/-- A dictionary's basic solution is feasible exactly when every row constant
is nonnegative. -/
def IsBasicFeasible (D : Dictionary m n) : Prop :=
  ∀ i, 0 ≤ D.b i

end Dictionary
end Chapter29
end CLRS
