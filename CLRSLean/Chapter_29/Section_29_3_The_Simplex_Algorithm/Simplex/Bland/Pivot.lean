import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Equivalence

/-!
# 29.3 Certified Bland pivots

This module packages one nonterminal SIMPLEX step as a binary relation and
records its local basis, feasibility, objective, and basic-solution effects.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- The data and certificates carried by one Bland-rule PIVOT. -/
structure BlandPivot (D E : Dictionary m n) where
  entering : Fin n
  leaving : Fin m
  enteringIsBland : D.IsBlandEntering entering
  leavingIsBland : D.IsBlandLeaving entering leaving
  next_eq : E = D.pivot leaving entering
    leavingIsBland.1.pivotCoefficient_pos.ne'

/-- The proposition-valued edge relation induced by certified Bland pivots. -/
def IsBlandPivot (D E : Dictionary m n) : Prop :=
  Nonempty (BlandPivot D E)

/-- Exact basis membership after exchanging one entering and one leaving
variable. -/
theorem mem_basicVariables_pivot_iff (D : Dictionary m n)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) (q : LPVar m n) :
    q ∈ (D.pivot l e h).basicVariables ↔
      q = D.nonbasicVar e ∨
        (q ∈ D.basicVariables ∧ q ≠ D.basicVar l) := by
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := ((D.pivot l e h).mem_basicVariables q).1 hq
    by_cases hil : i = l
    · subst i
      left
      exact hi.symm.trans (D.pivot_basicVar_leaving l e h)
    · right
      constructor
      · exact (D.mem_basicVariables q).2
          ⟨i, (D.pivot_basicVar_of_ne l i e h hil).symm.trans hi⟩
      · intro hleave
        have : D.basicVar i = D.basicVar l :=
          (D.pivot_basicVar_of_ne l i e h hil).symm.trans
            (hi.trans hleave)
        have hslots := D.labels.injective this
        exact hil (Sum.inl_injective hslots)
  · rintro (rfl | ⟨hq, hne⟩)
    · exact ((D.pivot l e h).mem_basicVariables _).2
        ⟨l, D.pivot_basicVar_leaving l e h⟩
    · obtain ⟨i, hi⟩ := (D.mem_basicVariables q).1 hq
      have hil : i ≠ l := by
        intro hil
        subst i
        exact hne hi.symm
      exact ((D.pivot l e h).mem_basicVariables q).2
        ⟨i, (D.pivot_basicVar_of_ne l i e h hil).trans hi⟩

namespace BlandPivot

/-- The selected entering variable is outside the old basis. -/
theorem entering_not_mem (p : BlandPivot D E) :
    D.nonbasicVar p.entering ∉ D.basicVariables :=
  D.nonbasicVar_not_mem_basicVariables p.entering

/-- The selected entering variable belongs to the new basis. -/
theorem entering_mem (p : BlandPivot D E) :
    D.nonbasicVar p.entering ∈ E.basicVariables := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  rw [D.mem_basicVariables_pivot_iff]
  exact Or.inl rfl

/-- The selected leaving variable belongs to the old basis. -/
theorem leaving_mem (p : BlandPivot D E) :
    D.basicVar p.leaving ∈ D.basicVariables :=
  D.basicVar_mem_basicVariables p.leaving

/-- The selected leaving variable is outside the new basis. -/
theorem leaving_not_mem (p : BlandPivot D E) :
    D.basicVar p.leaving ∉ E.basicVariables := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  rw [D.mem_basicVariables_pivot_iff]
  rintro (henter | ⟨_, hleave⟩)
  · exact D.labels_basic_ne_nonbasic l e henter
  · exact hleave rfl

/-- A variable that enters the basis across a pivot is exactly the selected
entering variable. -/
theorem eq_entering_of_not_mem_mem {m n : ℕ}
    {D E : Dictionary m n} (p : BlandPivot D E) {q : LPVar m n}
    (hbefore : q ∉ D.basicVariables) (hafter : q ∈ E.basicVariables) :
    q = D.nonbasicVar p.entering := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  rcases (D.mem_basicVariables_pivot_iff l e _ q).1 hafter with
    henter | ⟨hold, _⟩
  · exact henter
  · exact False.elim (hbefore hold)

/-- A variable that leaves the basis across a pivot is exactly the selected
leaving variable. -/
theorem eq_leaving_of_mem_not_mem {m n : ℕ}
    {D E : Dictionary m n} (p : BlandPivot D E) {q : LPVar m n}
    (hbefore : q ∈ D.basicVariables) (hafter : q ∉ E.basicVariables) :
    q = D.basicVar p.leaving := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  by_contra hne
  apply hafter
  exact (D.mem_basicVariables_pivot_iff l e _ q).2
    (Or.inr ⟨hbefore, hne⟩)

/-- Every Bland pivot preserves the represented equations and objective. -/
theorem equivalent (p : BlandPivot D E) : D.Equivalent E := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  exact D.pivot_equivalent l e hl.1.pivotCoefficient_pos.ne'

/-- Every Bland pivot preserves basic feasibility. -/
theorem isBasicFeasible (p : BlandPivot D E)
    (hD : D.IsBasicFeasible) : E.IsBasicFeasible := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  exact D.pivot_isBasicFeasible e l hD hl.1

/-- Every feasible Bland pivot has nondecreasing basic objective value. -/
theorem v_mono (p : BlandPivot D E) (hD : D.IsBasicFeasible) :
    D.v ≤ E.v := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  exact D.pivot_v_mono hD he.1 hl.1

/-- A Bland pivot whose objective constant does not change is degenerate. -/
theorem leavingValue_eq_zero_of_v_eq (p : BlandPivot D E)
    (hD : D.IsBasicFeasible) (hv : D.v = E.v) : D.b p.leaving = 0 := by
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  have hnonpos : ¬0 < D.b l := by
    intro hpos
    have hstrict : D.v < (D.pivot l e
        hl.1.pivotCoefficient_pos.ne').v :=
      D.pivot_v_strict he.1 hpos hl.1
    exact (ne_of_lt hstrict) hv
  exact le_antisymm (le_of_not_gt hnonpos) (hD l)

/-- A degenerate Bland pivot leaves the complete basic assignment unchanged. -/
theorem basicAssignment_eq_of_v_eq (p : BlandPivot D E)
    (hD : D.IsBasicFeasible) (hv : D.v = E.v) :
    D.basicAssignment = E.basicAssignment := by
  have hb : D.b p.leaving = 0 := p.leavingValue_eq_zero_of_v_eq hD hv
  rcases p with ⟨e, l, he, hl, hnext⟩
  subst E
  let hne := hl.1.pivotCoefficient_pos.ne'
  let next := D.pivot l e hne
  have hsat : next.Satisfies D.basicAssignment :=
    ((D.pivot_equivalent l e hne).1
      D.basicAssignment).1 D.basicAssignment_satisfies
  apply next.eq_basicAssignment_of_satisfies_of_nonbasic_zero hsat
  intro j
  by_cases hj : j = e
  · subst j
    rw [D.pivot_nonbasicVar_entering l e hne]
    simpa using hb
  · rw [D.pivot_nonbasicVar_of_ne l e j hne hj]
    exact D.basicAssignment_nonbasicVar j

end BlandPivot

end Dictionary
end Chapter29
end CLRS
