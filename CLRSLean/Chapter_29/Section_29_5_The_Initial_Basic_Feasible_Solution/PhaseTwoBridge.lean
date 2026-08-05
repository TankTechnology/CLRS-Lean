import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseTwoStart

/-!
# 29.5 Projecting phase II back to the original program

The lock forces the artificial coordinate to zero.  Therefore optimality and
unboundedness of the phase-II program project directly to the original LP.
-/

namespace CLRS
namespace Chapter29

namespace StandardLP

/-- An optimal locked-auxiliary assignment projects to an optimal original
assignment. -/
theorem lockedAuxiliary_optimal_to_original (P : StandardLP m n)
    {z : Fin (n + 1) → ℝ} (hz : P.lockedAuxiliary.IsOptimal z) :
    P.IsOptimal (auxiliaryTail z) := by
  have hzparts := (P.lockedAuxiliary_feasible_iff z).1 hz.1
  refine ⟨hzparts.2, ?_⟩
  intro x hx
  let u := auxiliaryAssignment 0 x
  have hu : P.lockedAuxiliary.IsFeasible u :=
    (P.lockedAuxiliary_feasible_iff u).2 ⟨rfl, by simpa [u]⟩
  have hle := hz.2 u hu
  rw [P.lockedAuxiliary_objective u,
    P.lockedAuxiliary_objective z] at hle
  simpa [u] using hle

/-- An unbounded locked-auxiliary program makes the original program
unbounded. -/
theorem lockedAuxiliary_unbounded_to_original (P : StandardLP m n)
    (h : P.lockedAuxiliary.IsUnbounded) : P.IsUnbounded := by
  intro M
  obtain ⟨z, hz, hlarge⟩ := h M
  have hzparts := (P.lockedAuxiliary_feasible_iff z).1 hz
  refine ⟨auxiliaryTail z, hzparts.2, ?_⟩
  rw [← P.lockedAuxiliary_objective z]
  exact hlarge

end StandardLP
end Chapter29
end CLRS
