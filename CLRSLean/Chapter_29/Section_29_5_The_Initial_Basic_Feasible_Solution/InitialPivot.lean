import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.ArtificialLP

/-!
# 29.5 The initial artificial-variable pivot

If some right-hand side is negative, the textbook chooses a most-negative
row and pivots the artificial variable into that row.  The resulting
auxiliary dictionary is basic feasible.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- A row attaining the minimum right-hand side, together with the fact that
this minimum is negative. -/
structure MostNegativeRow (P : StandardLP m n) where
  row : Fin m
  negative : P.b row < 0
  minimal : ∀ i, P.b row ≤ P.b i

/-- Select a most-negative row whenever one exists. -/
noncomputable def mostNegativeRow (P : StandardLP m n)
    (hneg : ∃ i, P.b i < 0) : P.MostNegativeRow := by
  let w := Classical.choose hneg
  have hw : P.b w < 0 := Classical.choose_spec hneg
  have huniv : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨w, Finset.mem_univ w⟩
  have hexists :=
    (Finset.univ : Finset (Fin m)).exists_min_image P.b huniv
  let l := Classical.choose hexists
  have hlspec := Classical.choose_spec hexists
  have hminimal : ∀ i ∈ (Finset.univ : Finset (Fin m)), P.b l ≤ P.b i :=
    hlspec.2
  refine ⟨l, ?_, fun i => hminimal i (Finset.mem_univ i)⟩
  exact lt_of_le_of_lt (hminimal w (Finset.mem_univ w)) hw

/-- The dictionary obtained by the prescribed initial pivot on {lit}`x₀`. -/
noncomputable def auxiliaryPivotedDictionary (P : StandardLP m n)
    (hneg : ∃ i, P.b i < 0) : Dictionary m (n + 1) :=
  let l := (P.mostNegativeRow hneg).row
  P.auxiliary.initialDictionary.pivot l (auxiliaryArtificial n) (by
    change (-1 : ℝ) ≠ 0
    norm_num)

/-- The prescribed artificial-variable pivot produces nonnegative basic
constants. -/
theorem auxiliaryPivotedDictionary_isBasicFeasible (P : StandardLP m n)
    (hneg : ∃ i, P.b i < 0) :
    (P.auxiliaryPivotedDictionary hneg).IsBasicFeasible := by
  let l := (P.mostNegativeRow hneg).row
  have hlneg : P.b l < 0 := (P.mostNegativeRow hneg).negative
  have hlmin : ∀ i, P.b l ≤ P.b i := (P.mostNegativeRow hneg).minimal
  intro i
  by_cases hi : i = l
  · subst i
    simp only [auxiliaryPivotedDictionary, l,
      Dictionary.pivot_b_leaving]
    change 0 ≤ P.b l / (-1 : ℝ)
    linarith
  · rw [auxiliaryPivotedDictionary, Dictionary.pivot_b_of_ne _ l i _ _ hi]
    change 0 ≤ P.b i - (-1 : ℝ) * (P.b l / (-1 : ℝ))
    have hle := hlmin i
    linarith

/-- The initial pivot changes only the dictionary representation, not the
auxiliary feasible region or objective. -/
theorem auxiliaryPivotedDictionary_equivalent (P : StandardLP m n)
    (hneg : ∃ i, P.b i < 0) :
    P.auxiliary.initialDictionary.Equivalent
      (P.auxiliaryPivotedDictionary hneg) := by
  let l := (P.mostNegativeRow hneg).row
  exact P.auxiliary.initialDictionary.pivot_equivalent l
    (auxiliaryArtificial n) (by
      change (-1 : ℝ) ≠ 0
      norm_num)

/-- Textbook phase-I start: pivot {lit}`x₀` only when the ordinary initial
dictionary has a negative basic value. -/
noncomputable def phaseOneStart (P : StandardLP m n) : Dictionary m (n + 1) :=
  if hneg : ∃ i, P.b i < 0 then P.auxiliaryPivotedDictionary hneg
  else P.auxiliary.initialDictionary

/-- The phase-I starting dictionary is always basic feasible. -/
theorem phaseOneStart_isBasicFeasible (P : StandardLP m n) :
    P.phaseOneStart.IsBasicFeasible := by
  by_cases hneg : ∃ i, P.b i < 0
  · simpa [phaseOneStart, hneg] using
      P.auxiliaryPivotedDictionary_isBasicFeasible hneg
  · rw [phaseOneStart, dif_neg hneg]
    intro i
    change 0 ≤ P.b i
    exact le_of_not_gt (fun hi => hneg ⟨i, hi⟩)

/-- The phase-I start is equivalent to the auxiliary initial dictionary. -/
theorem phaseOneStart_equivalent_auxiliary (P : StandardLP m n) :
    P.auxiliary.initialDictionary.Equivalent P.phaseOneStart := by
  by_cases hneg : ∃ i, P.b i < 0
  · simpa [phaseOneStart, hneg] using
      P.auxiliaryPivotedDictionary_equivalent hneg
  · simpa [phaseOneStart, hneg] using
      Dictionary.Equivalent.refl P.auxiliary.initialDictionary

end StandardLP
end Chapter29
end CLRS
