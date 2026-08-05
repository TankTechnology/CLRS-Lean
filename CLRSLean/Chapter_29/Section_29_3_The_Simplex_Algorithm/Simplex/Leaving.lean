import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Entering

/-!
# 29.3 Minimum-ratio and Bland leaving-variable selection

After fixing an entering column, SIMPLEX considers exactly the rows with a
positive coefficient, minimizes their ratios, and uses the least stable basic
variable identity to break ties.
-/

namespace CLRS
namespace Chapter29

namespace Dictionary

/-- Rows that impose a finite upper bound on the entering variable. -/
noncomputable def positiveRows (D : Dictionary m n) (e : Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => 0 < D.a i e

/-- Rows attaining the minimum positive-coefficient ratio. -/
noncomputable def minimumRatioRows (D : Dictionary m n) (e : Fin n) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => D.IsMinimumRatio e i

@[simp] theorem mem_positiveRows (D : Dictionary m n) (e : Fin n) (i : Fin m) :
    i ∈ D.positiveRows e ↔ 0 < D.a i e := by
  simp [positiveRows]

@[simp] theorem mem_minimumRatioRows (D : Dictionary m n)
    (e : Fin n) (i : Fin m) :
    i ∈ D.minimumRatioRows e ↔ D.IsMinimumRatio e i := by
  simp [minimumRatioRows]

/-- A finite nonempty set of constraining rows contains a minimum-ratio row. -/
theorem exists_isMinimumRatio_of_exists_pos (D : Dictionary m n) (e : Fin n)
    (hpos : ∃ i, 0 < D.a i e) : ∃ l, D.IsMinimumRatio e l := by
  let rows := D.positiveRows e
  let ratio : Fin m → ℝ := fun i => D.b i / D.a i e
  have hrows : rows.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simpa [rows] using hi⟩
  have himage : (rows.image ratio).Nonempty := hrows.image ratio
  let r := (rows.image ratio).min' himage
  have hrmem : r ∈ rows.image ratio :=
    Finset.min'_mem (rows.image ratio) himage
  obtain ⟨l, hlrows, hlr⟩ := Finset.mem_image.mp hrmem
  refine ⟨l, ?_, ?_⟩
  · exact (D.mem_positiveRows e l).1 (by simpa [rows] using hlrows)
  · intro i hi
    have hirows : i ∈ rows := by
      simpa [rows] using (D.mem_positiveRows e i).2 hi
    have hiimage : ratio i ∈ rows.image ratio :=
      Finset.mem_image.mpr ⟨i, hirows, rfl⟩
    have hle : r ≤ ratio i := Finset.min'_le (rows.image ratio) _ hiimage
    simpa [ratio, ← hlr] using hle

/-- Minimum-ratio rows exist exactly when the entering column contains a
positive coefficient. -/
theorem minimumRatioRows_nonempty_iff (D : Dictionary m n) (e : Fin n) :
    (D.minimumRatioRows e).Nonempty ↔ ∃ i, 0 < D.a i e := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, ((D.mem_minimumRatioRows e l).1 hl).pivotCoefficient_pos⟩
  · intro hpos
    obtain ⟨l, hl⟩ := D.exists_isMinimumRatio_of_exists_pos e hpos
    exact ⟨l, (D.mem_minimumRatioRows e l).2 hl⟩

/-- The textbook second half of Bland's rule. -/
def IsBlandLeaving (D : Dictionary m n) (e : Fin n) (l : Fin m) : Prop :=
  D.IsMinimumRatio e l ∧ ∀ i, D.IsMinimumRatio e i →
    D.basicVariableIndex l ≤ D.basicVariableIndex i

/-- The order on basic slots induced by their stable variable identities. -/
@[reducible] noncomputable def basicBlandOrder
    (D : Dictionary m n) : LinearOrder (Fin m) :=
  LinearOrder.lift' D.basicVariableIndex D.basicVariableIndex_injective

/-- Select the least stable basic identity among all minimum-ratio rows. -/
noncomputable def blandLeaving? (D : Dictionary m n) (e : Fin n) :
    Option (Fin m) :=
  if h : (D.minimumRatioRows e).Nonempty then
    letI := D.basicBlandOrder
    some ((D.minimumRatioRows e).min' h)
  else
    none

/-- Returning {lit}`none` means that the entering column has no positive
coefficient and therefore imposes no finite ratio bound. -/
theorem blandLeaving?_eq_none_iff (D : Dictionary m n) (e : Fin n) :
    D.blandLeaving? e = none ↔ ∀ i, D.a i e ≤ 0 := by
  rw [show (∀ i, D.a i e ≤ 0) ↔ ¬ ∃ i, 0 < D.a i e by
    simp only [not_exists, not_lt]]
  rw [← D.minimumRatioRows_nonempty_iff e]
  constructor
  · intro hnone hne
    simp [blandLeaving?, hne] at hnone
  · intro hempty
    simp [blandLeaving?, hempty]

/-- Every selected leaving row realizes the minimum ratio and Bland's stable
identity tie break. -/
theorem blandLeaving?_spec (D : Dictionary m n) (e : Fin n) {l : Fin m}
    (hsel : D.blandLeaving? e = some l) : D.IsBlandLeaving e l := by
  unfold blandLeaving? at hsel
  split at hsel
  next hne =>
    letI := D.basicBlandOrder
    simp only [Option.some.injEq] at hsel
    subst l
    constructor
    · exact (D.mem_minimumRatioRows e _).1
        (Finset.min'_mem (D.minimumRatioRows e) hne)
    · intro i hi
      have himem : i ∈ D.minimumRatioRows e :=
        (D.mem_minimumRatioRows e i).2 hi
      have hle := Finset.min'_le (D.minimumRatioRows e) i himem
      exact hle
  next hempty =>
    cases hsel

end Dictionary
end Chapter29
end CLRS
