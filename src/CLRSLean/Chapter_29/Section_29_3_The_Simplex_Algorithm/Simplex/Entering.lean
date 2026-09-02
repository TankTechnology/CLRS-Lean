import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.VariableOrder

/-!
# 29.3 Bland entering-variable selection

The entering variable is the least canonical variable identity among all
nonbasic columns with positive reduced cost.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Nonbasic slots whose reduced cost permits objective improvement. -/
noncomputable def enteringCandidates (D : Dictionary m n) : Finset (Fin n) :=
  Finset.univ.filter fun j => 0 < D.c j

/-- The textbook first half of Bland's rule. -/
def IsBlandEntering (D : Dictionary m n) (e : Fin n) : Prop :=
  0 < D.c e ∧ ∀ j, 0 < D.c j →
    D.nonbasicVariableIndex e ≤ D.nonbasicVariableIndex j

/-- The order on nonbasic slots induced by their stable variable identities. -/
@[reducible] noncomputable def nonbasicBlandOrder
    (D : Dictionary m n) : LinearOrder (Fin n) :=
  LinearOrder.lift' D.nonbasicVariableIndex D.nonbasicVariableIndex_injective

/-- Deterministically select Bland's entering slot, or return {lit}`none` when the
dictionary has no positive reduced cost. -/
noncomputable def blandEntering? (D : Dictionary m n) : Option (Fin n) :=
  if h : D.enteringCandidates.Nonempty then
    letI := D.nonbasicBlandOrder
    some (D.enteringCandidates.min' h)
  else
    none

/-- Candidate membership is exactly reduced-cost positivity. -/
@[simp] theorem mem_enteringCandidates (D : Dictionary m n) (j : Fin n) :
    j ∈ D.enteringCandidates ↔ 0 < D.c j := by
  simp [enteringCandidates]

/-- Returning {lit}`none` is exactly the textbook optimal-exit coefficient test. -/
theorem blandEntering?_eq_none_iff (D : Dictionary m n) :
    D.blandEntering? = none ↔ ∀ j, D.c j ≤ 0 := by
  constructor
  · intro hnone j
    by_contra hnot
    have hpos : 0 < D.c j := lt_of_not_ge hnot
    have hne : D.enteringCandidates.Nonempty :=
      ⟨j, (D.mem_enteringCandidates j).2 hpos⟩
    simp [blandEntering?, hne] at hnone
  · intro hall
    have hempty : ¬ D.enteringCandidates.Nonempty := by
      intro hne
      obtain ⟨j, hj⟩ := hne
      have hpos : 0 < D.c j := (D.mem_enteringCandidates j).1 hj
      exact (not_lt_of_ge (hall j)) hpos
    simp [blandEntering?, hempty]

/-- Every selected entering slot has positive reduced cost and is least by
stable variable identity among all improving slots. -/
theorem blandEntering?_spec (D : Dictionary m n) {e : Fin n}
    (hsel : D.blandEntering? = some e) : D.IsBlandEntering e := by
  unfold blandEntering? at hsel
  split at hsel
  next hne =>
    letI := D.nonbasicBlandOrder
    simp only [Option.some.injEq] at hsel
    subst e
    constructor
    · exact (D.mem_enteringCandidates _).1
        (Finset.min'_mem D.enteringCandidates hne)
    · intro j hj
      have hjmem : j ∈ D.enteringCandidates :=
        (D.mem_enteringCandidates j).2 hj
      have hle := Finset.min'_le D.enteringCandidates j hjmem
      exact hle
  next hempty =>
    cases hsel

end Dictionary
end Chapter29
end CLRS
