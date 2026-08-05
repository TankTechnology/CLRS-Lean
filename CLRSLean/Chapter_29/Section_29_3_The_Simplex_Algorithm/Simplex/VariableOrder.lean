import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot

/-!
# 29.3 Canonical variable order for Bland's rule

Bland's rule compares stable original/slack variable identities rather than
the row or column slots that change meaning after every PIVOT.
-/

namespace CLRS
namespace Chapter29

/-- The canonical zero-based CLRS variable index: original variables precede
slack variables. -/
def variableIndex {m n : ℕ} : LPVar m n → ℕ
  | .inl j => j.1
  | .inr i => n + i.1

/-- Every canonical variable index lies in the {lit}`n + m` variable universe. -/
theorem variableIndex_lt {m n : ℕ} (q : LPVar m n) :
    variableIndex q < n + m := by
  cases q with
  | inl j =>
      simp only [variableIndex]
      omega
  | inr i =>
      simp only [variableIndex]
      omega

/-- The canonical index uniquely identifies an original or slack variable. -/
theorem variableIndex_injective {m n : ℕ} :
    Function.Injective (@variableIndex m n) := by
  intro q r h
  cases q with
  | inl j =>
      cases r with
      | inl k =>
          have hjk : j = k := Fin.ext (by simpa only [variableIndex] using h)
          exact congrArg Sum.inl hjk
      | inr i =>
          simp only [variableIndex] at h
          omega
  | inr i =>
      cases r with
      | inl j =>
          simp only [variableIndex] at h
          omega
      | inr k =>
          simp only [variableIndex] at h
          have hik : i = k := Fin.ext (by omega)
          exact congrArg Sum.inr hik

namespace Dictionary

/-- Stable canonical index of the variable occupying a basic row. -/
def basicVariableIndex (D : Dictionary m n) (i : Fin m) : ℕ :=
  variableIndex (D.basicVar i)

/-- Stable canonical index of the variable occupying a nonbasic column. -/
def nonbasicVariableIndex (D : Dictionary m n) (j : Fin n) : ℕ :=
  variableIndex (D.nonbasicVar j)

/-- Different basic rows contain different canonical variable identities. -/
theorem basicVariableIndex_injective (D : Dictionary m n) :
    Function.Injective D.basicVariableIndex := by
  intro i k h
  have hv : D.basicVar i = D.basicVar k := variableIndex_injective h
  have hs : (Sum.inl i : Fin m ⊕ Fin n) = Sum.inl k := D.labels.injective hv
  exact Sum.inl_injective hs

/-- Different nonbasic columns contain different canonical variable identities. -/
theorem nonbasicVariableIndex_injective (D : Dictionary m n) :
    Function.Injective D.nonbasicVariableIndex := by
  intro j k h
  have hv : D.nonbasicVar j = D.nonbasicVar k := variableIndex_injective h
  have hs : (Sum.inr j : Fin m ⊕ Fin n) = Sum.inr k := D.labels.injective hv
  exact Sum.inr_injective hs

end Dictionary
end Chapter29
end CLRS
