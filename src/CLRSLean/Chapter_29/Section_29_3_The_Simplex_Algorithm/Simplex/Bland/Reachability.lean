import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Pivot

/-!
# 29.3 Bland-pivot reachability

The reflexive-transitive closure of certified Bland pivots is the trace model
used by the anti-cycling proof.  This module lifts the local pivot invariants
and locates the step where a variable crosses the basis boundary.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Reachability by zero or more certified Bland pivots. -/
abbrev BlandReachable (D E : Dictionary m n) : Prop :=
  Relation.ReflTransGen IsBlandPivot D E

namespace BlandReachable

/-- Concatenation of Bland-pivot traces. -/
theorem trans (hDE : BlandReachable D E) (hEF : BlandReachable E F) :
    BlandReachable D F :=
  Relation.ReflTransGen.trans hDE hEF

/-- A single certified pivot is a reachable step. -/
theorem single (p : BlandPivot D E) : BlandReachable D E :=
  Relation.ReflTransGen.single ⟨p⟩

/-- Every dictionary on a Bland trace is equivalent to its start. -/
theorem equivalent (h : BlandReachable D E) : D.Equivalent E := by
  induction h with
  | refl => exact Equivalent.refl D
  | tail hDA hAE ih =>
      obtain ⟨p⟩ := hAE
      exact ih.trans p.equivalent

/-- Basic feasibility propagates along a Bland trace. -/
theorem isBasicFeasible (h : BlandReachable D E)
    (hD : D.IsBasicFeasible) : E.IsBasicFeasible := by
  induction h with
  | refl => exact hD
  | tail _ hAE ih =>
      obtain ⟨p⟩ := hAE
      exact p.isBasicFeasible ih

/-- The basic objective value is nondecreasing along a feasible Bland trace. -/
theorem v_mono (h : BlandReachable D E) (hD : D.IsBasicFeasible) :
    D.v ≤ E.v := by
  induction h with
  | refl => exact le_rfl
  | tail hDA hAE ih =>
      obtain ⟨p⟩ := hAE
      have hA : _ := BlandReachable.isBasicFeasible hDA hD
      exact ih.trans (p.v_mono hA)

/-- If a feasible trace has equal endpoint objective constants, every pivot
is degenerate and the endpoint basic assignments coincide. -/
theorem basicAssignment_eq_of_v_eq (h : BlandReachable D E)
    (hD : D.IsBasicFeasible) (hv : D.v = E.v) :
    D.basicAssignment = E.basicAssignment := by
  induction h with
  | refl => rfl
  | @tail A B hDA hAB ih =>
      obtain ⟨p⟩ := hAB
      have hA : A.IsBasicFeasible :=
        BlandReachable.isBasicFeasible hDA hD
      have hDAle : D.v ≤ A.v := BlandReachable.v_mono hDA hD
      have hABle : A.v ≤ B.v := p.v_mono hA
      have hDAeq : D.v = A.v := le_antisymm hDAle (by
        calc
          A.v ≤ B.v := hABle
          _ = D.v := hv.symm)
      have hABeq : A.v = B.v := le_antisymm hABle (by
        calc
          B.v = D.v := hv.symm
          _ ≤ A.v := hDAle)
      exact (ih hDAeq).trans (p.basicAssignment_eq_of_v_eq hA hABeq)

/-- If a variable is outside the first basis and inside the last basis, some
pivot on the trace selected it as entering. -/
theorem exists_entering_of_not_mem_mem {m n : ℕ}
    {D E : Dictionary m n} (h : BlandReachable D E) {q : LPVar m n}
    (hbefore : q ∉ D.basicVariables) (hafter : q ∈ E.basicVariables) :
    ∃ (A B : Dictionary m n) (p : BlandPivot A B),
      BlandReachable D A ∧ BlandReachable B E ∧
        q = A.nonbasicVar p.entering := by
  induction h with
  | refl => exact False.elim (hbefore hafter)
  | @tail A B hDA hAB ih =>
      obtain ⟨p⟩ := hAB
      by_cases hqA : q ∈ A.basicVariables
      · obtain ⟨X, Y, px, hDX, hYA, hq⟩ := ih hqA
        exact ⟨X, Y, px, hDX, hYA.tail ⟨p⟩, hq⟩
      · exact ⟨A, B, p, hDA, Relation.ReflTransGen.refl,
          p.eq_entering_of_not_mem_mem hqA hafter⟩

/-- If a variable is inside the first basis and outside the last basis, some
pivot on the trace selected it as leaving. -/
theorem exists_leaving_of_mem_not_mem {m n : ℕ}
    {D E : Dictionary m n} (h : BlandReachable D E) {q : LPVar m n}
    (hbefore : q ∈ D.basicVariables) (hafter : q ∉ E.basicVariables) :
    ∃ (A B : Dictionary m n) (p : BlandPivot A B),
      BlandReachable D A ∧ BlandReachable B E ∧
        q = A.basicVar p.leaving := by
  induction h with
  | refl => exact False.elim (hafter hbefore)
  | @tail A B hDA hAB ih =>
      obtain ⟨p⟩ := hAB
      by_cases hqA : q ∈ A.basicVariables
      · exact ⟨A, B, p, hDA, Relation.ReflTransGen.refl,
          p.eq_leaving_of_mem_not_mem hqA hafter⟩
      · obtain ⟨X, Y, px, hDX, hYA, hq⟩ := ih hqA
        exact ⟨X, Y, px, hDX, hYA.tail ⟨p⟩, hq⟩

end BlandReachable

end Dictionary
end Chapter29
end CLRS
