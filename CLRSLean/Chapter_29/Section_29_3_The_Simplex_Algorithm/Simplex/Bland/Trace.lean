import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Reachability

/-!
# 29.3 Fickle variables on Bland traces

A variable is fickle on a closed trace when some intermediate dictionary has
the opposite basis status from the start.  This is the finite set from which
the textbook proof chooses its greatest-index variable.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- A dictionary together with a prefix and suffix locating it on a trace. -/
def OnBlandPath (D E F : Dictionary m n) : Prop :=
  BlandReachable D E ∧ BlandReachable E F

namespace OnBlandPath

/-- Concatenate the prefix and suffix of an on-path witness. -/
theorem whole (h : OnBlandPath D E F) : BlandReachable D F :=
  h.1.trans h.2

/-- Every on-path dictionary is feasible when the trace start is feasible. -/
theorem isBasicFeasible (h : OnBlandPath D E F)
    (hD : D.IsBasicFeasible) : E.IsBasicFeasible :=
  h.1.isBasicFeasible hD

/-- On a closed-basis feasible trace, every intermediate dictionary has the
same basic objective constant as the start. -/
theorem v_eq_of_closedBasis (h : OnBlandPath D E F)
    (hD : D.IsBasicFeasible) (hbasis : D.basicVariables = F.basicVariables) :
    D.v = E.v := by
  have hvDF : D.v = F.v :=
    h.whole.equivalent.v_eq_of_basicVariables_eq hbasis
  have hDE : D.v ≤ E.v := h.1.v_mono hD
  have hE : E.IsBasicFeasible := h.isBasicFeasible hD
  have hEF : E.v ≤ F.v := h.2.v_mono hE
  exact le_antisymm hDE (by
    calc
      E.v ≤ F.v := hEF
      _ = D.v := hvDF.symm)

/-- Degeneracy along a closed-basis trace makes every intermediate basic
assignment equal to the start assignment. -/
theorem basicAssignment_eq_of_closedBasis (h : OnBlandPath D E F)
    (hD : D.IsBasicFeasible) (hbasis : D.basicVariables = F.basicVariables) :
    D.basicAssignment = E.basicAssignment :=
  h.1.basicAssignment_eq_of_v_eq hD (h.v_eq_of_closedBasis hD hbasis)

end OnBlandPath

/-- A variable whose basis status changes at some point of a fixed trace. -/
def IsFickle (D F : Dictionary m n) (q : LPVar m n) : Prop :=
  ∃ E, OnBlandPath D E F ∧
    ((q ∈ D.basicVariables ∧ q ∉ E.basicVariables) ∨
      (q ∉ D.basicVariables ∧ q ∈ E.basicVariables))

/-- The finite set of fickle variables on a trace. -/
noncomputable def fickleVariables (D F : Dictionary m n) :
    Finset (LPVar m n) := by
  classical
  exact Finset.univ.filter (D.IsFickle F)

@[simp] theorem mem_fickleVariables (D F : Dictionary m n) (q : LPVar m n) :
    q ∈ D.fickleVariables F ↔ D.IsFickle F q := by
  classical
  simp [fickleVariables]

/-- Every entering variable of an on-path pivot is fickle. -/
theorem isFickle_entering (hDA : BlandReachable D A)
    (p : BlandPivot A B) (hBF : BlandReachable B F) :
    D.IsFickle F (A.nonbasicVar p.entering) := by
  let q := A.nonbasicVar p.entering
  by_cases hqD : q ∈ D.basicVariables
  · refine ⟨A, ⟨hDA, (BlandReachable.single p).trans hBF⟩,
        Or.inl ⟨hqD, ?_⟩⟩
    exact p.entering_not_mem
  · refine ⟨B, ⟨hDA.trans (BlandReachable.single p), hBF⟩,
        Or.inr ⟨hqD, ?_⟩⟩
    exact p.entering_mem

/-- Every leaving variable of an on-path pivot is fickle. -/
theorem isFickle_leaving (hDA : BlandReachable D A)
    (p : BlandPivot A B) (hBF : BlandReachable B F) :
    D.IsFickle F (A.basicVar p.leaving) := by
  let q := A.basicVar p.leaving
  by_cases hqD : q ∈ D.basicVariables
  · refine ⟨B, ⟨hDA.trans (BlandReachable.single p), hBF⟩,
        Or.inl ⟨hqD, ?_⟩⟩
    exact p.leaving_not_mem
  · refine ⟨A, ⟨hDA, (BlandReachable.single p).trans hBF⟩,
        Or.inr ⟨hqD, ?_⟩⟩
    exact p.leaving_mem

/-- A nonempty closed pivot trace always has a fickle variable. -/
theorem fickleVariables_nonempty_of_cycle {D F : Dictionary m n}
    (hcycle : Relation.TransGen IsBlandPivot D F) :
    (D.fickleVariables F).Nonempty := by
  obtain ⟨E, hDE, hEF⟩ := Relation.TransGen.head'_iff.mp hcycle
  obtain ⟨p⟩ := hDE
  refine ⟨D.nonbasicVar p.entering, (D.mem_fickleVariables F _).2 ?_⟩
  exact ⟨E, ⟨BlandReachable.single p, hEF⟩,
    Or.inr ⟨p.entering_not_mem, p.entering_mem⟩⟩

/-- The greatest-index fickle variable selected in the textbook proof. -/
noncomputable def greatestFickle (D F : Dictionary m n)
    (hne : (D.fickleVariables F).Nonempty) : LPVar m n := by
  letI := variableBlandOrder m n
  exact (D.fickleVariables F).max' hne

/-- The selected greatest fickle variable is itself fickle. -/
theorem greatestFickle_mem (D F : Dictionary m n)
    (hne : (D.fickleVariables F).Nonempty) :
    D.greatestFickle F hne ∈ D.fickleVariables F := by
  letI := variableBlandOrder m n
  exact Finset.max'_mem (D.fickleVariables F) hne

/-- Every fickle variable has index at most the selected greatest index. -/
theorem variableIndex_le_greatestFickle (D F : Dictionary m n)
    (hne : (D.fickleVariables F).Nonempty) {q : LPVar m n}
    (hq : q ∈ D.fickleVariables F) :
    variableIndex q ≤ variableIndex (D.greatestFickle F hne) := by
  letI := variableBlandOrder m n
  exact Finset.le_max' (D.fickleVariables F) q hq

end Dictionary
end Chapter29
end CLRS
