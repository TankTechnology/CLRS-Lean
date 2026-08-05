import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Unboundedness

/-!
# 29.3 Equivalence of SIMPLEX dictionaries

Equivalent dictionaries represent exactly the same equation solutions and the
same objective expression on those solutions.  This packages the invariant
preserved by every PIVOT and later by the full SIMPLEX run.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Two dictionaries represent the same equations and objective function. -/
def Equivalent (D E : Dictionary m n) : Prop :=
  (∀ x, D.Satisfies x ↔ E.Satisfies x) ∧
    ∀ x, D.Satisfies x → D.objectiveRhs x = E.objectiveRhs x

namespace Equivalent

/-- Dictionary equivalence is reflexive. -/
protected theorem refl (D : Dictionary m n) : D.Equivalent D :=
  ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩

/-- Dictionary equivalence is symmetric. -/
theorem symm {D E : Dictionary m n} (h : D.Equivalent E) : E.Equivalent D := by
  refine ⟨fun x => (h.1 x).symm, ?_⟩
  intro x hx
  exact (h.2 x ((h.1 x).2 hx)).symm

/-- Dictionary equivalence is transitive. -/
theorem trans {D E F : Dictionary m n}
    (hDE : D.Equivalent E) (hEF : E.Equivalent F) : D.Equivalent F := by
  refine ⟨fun x => (hDE.1 x).trans (hEF.1 x), ?_⟩
  intro x hx
  exact (hDE.2 x hx).trans (hEF.2 x ((hDE.1 x).1 hx))

end Equivalent

/-- One PIVOT produces an equivalent dictionary. -/
theorem pivot_equivalent (D : Dictionary m n) (l : Fin m) (e : Fin n)
    (h : D.a l e ≠ 0) : D.Equivalent (D.pivot l e h) := by
  refine ⟨fun x => D.pivot_satisfies_iff x l e h, ?_⟩
  intro x hx
  exact (D.pivot_objectiveRhs_eq x l e h hx).symm

/-- The finite set of stable variable identities currently in the basis. -/
def basicVariables (D : Dictionary m n) : Finset (LPVar m n) :=
  Finset.univ.image D.basicVar

@[simp] theorem mem_basicVariables (D : Dictionary m n) (q : LPVar m n) :
    q ∈ D.basicVariables ↔ ∃ i, D.basicVar i = q := by
  simp [basicVariables]

@[simp] theorem basicVar_mem_basicVariables (D : Dictionary m n) (i : Fin m) :
    D.basicVar i ∈ D.basicVariables :=
  (D.mem_basicVariables _).2 ⟨i, rfl⟩

theorem nonbasicVar_not_mem_basicVariables (D : Dictionary m n) (j : Fin n) :
    D.nonbasicVar j ∉ D.basicVariables := by
  rw [D.mem_basicVariables]
  rintro ⟨i, hi⟩
  exact D.labels_basic_ne_nonbasic i j hi

/-- A satisfying assignment is uniquely determined after all its nonbasic
values are set to zero. -/
theorem eq_basicAssignment_of_satisfies_of_nonbasic_zero (D : Dictionary m n)
    {x : LPVar m n → ℝ} (hx : D.Satisfies x)
    (hzero : ∀ j, x (D.nonbasicVar j) = 0) : x = D.basicAssignment := by
  funext q
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · calc
      x (D.basicVar i) = D.rowRhs x i := hx i
      _ = D.b i := by simp [rowRhs, hzero]
      _ = D.basicAssignment (D.basicVar i) :=
        (D.basicAssignment_basicVar i).symm
  · simpa using hzero j

/-- A variable outside the basis is zero in the basic assignment. -/
theorem basicAssignment_eq_zero_of_not_mem_basicVariables (D : Dictionary m n)
    {q : LPVar m n} (hq : q ∉ D.basicVariables) :
    D.basicAssignment q = 0 := by
  rcases D.exists_basic_or_nonbasic q with ⟨i, rfl⟩ | ⟨j, rfl⟩
  · exact False.elim (hq (D.basicVar_mem_basicVariables i))
  · exact D.basicAssignment_nonbasicVar j

namespace Equivalent

/-- Equivalent dictionaries with the same basis have the same basic
assignment. -/
theorem basicAssignment_eq_of_basicVariables_eq {D E : Dictionary m n}
    (h : D.Equivalent E) (hbasis : D.basicVariables = E.basicVariables) :
    D.basicAssignment = E.basicAssignment := by
  have hsatD : D.Satisfies E.basicAssignment :=
    (h.1 E.basicAssignment).2 E.basicAssignment_satisfies
  have hzero : ∀ j, E.basicAssignment (D.nonbasicVar j) = 0 := by
    intro j
    apply E.basicAssignment_eq_zero_of_not_mem_basicVariables
    rw [← hbasis]
    exact D.nonbasicVar_not_mem_basicVariables j
  exact (D.eq_basicAssignment_of_satisfies_of_nonbasic_zero hsatD hzero).symm

/-- Equivalent dictionaries with the same basis have the same basic objective
value. -/
theorem v_eq_of_basicVariables_eq {D E : Dictionary m n}
    (h : D.Equivalent E) (hbasis : D.basicVariables = E.basicVariables) :
    D.v = E.v := by
  have hassign := h.basicAssignment_eq_of_basicVariables_eq hbasis
  calc
    D.v = D.objectiveRhs D.basicAssignment :=
      D.objectiveRhs_basicAssignment.symm
    _ = E.objectiveRhs D.basicAssignment :=
      h.2 D.basicAssignment D.basicAssignment_satisfies
    _ = E.objectiveRhs E.basicAssignment := by rw [hassign]
    _ = E.v := E.objectiveRhs_basicAssignment

/-- Transport an optimal assignment from an equivalent dictionary back to the
original representation. -/
theorem isOptimalAssignment {D E : Dictionary m n} (h : D.Equivalent E)
    {x : LPVar m n → ℝ} (hx : E.IsOptimalAssignment x) :
    D.IsOptimalAssignment x := by
  have hsatD : D.Satisfies x := (h.1 x).2 hx.2.1
  refine ⟨hx.1, hsatD, ?_⟩
  intro y hy hysatD
  calc
    D.objectiveRhs y = E.objectiveRhs y := h.2 y hysatD
    _ ≤ E.objectiveRhs x := hx.2.2 y hy ((h.1 y).1 hysatD)
    _ = D.objectiveRhs x := (h.2 x hsatD).symm

/-- Transport unboundedness from an equivalent dictionary back to the original
representation. -/
theorem isUnbounded {D E : Dictionary m n} (h : D.Equivalent E)
    (hE : E.IsUnbounded) : D.IsUnbounded := by
  intro M
  obtain ⟨x, hxnonneg, hxsatE, hxobj⟩ := hE M
  have hxsatD : D.Satisfies x := (h.1 x).2 hxsatE
  refine ⟨x, hxnonneg, hxsatD, ?_⟩
  rw [h.2 x hxsatD]
  exact hxobj

end Equivalent

end Dictionary
end Chapter29
end CLRS
