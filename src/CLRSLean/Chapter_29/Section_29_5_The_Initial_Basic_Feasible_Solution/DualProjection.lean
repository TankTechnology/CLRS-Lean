import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitializedSimplex

/-!
# 29.5 Projecting phase-II dual certificates

The first dual coordinate belongs to the artificial lock row.  Removing it
preserves every original dual constraint and preserves the dual objective,
because the lock row has right-hand side zero.
-/

namespace CLRS
namespace Chapter29

open Matrix
open scoped BigOperators

namespace StandardLP

/-- Remove the dual coordinate belonging to the artificial lock row. -/
def lockedDualTail (y : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  fun i => y i.succ

/-- On an original column, locked and original transposed matrix products
agree after dropping the lock-row dual coordinate. -/
theorem lockedAuxiliary_dual_mulVec_original (P : StandardLP m n)
    (y : Fin (m + 1) → ℝ) (j : Fin n) :
    (P.lockedAuxiliary.A.transpose *ᵥ y) (auxiliaryOriginal j) =
      (P.A.transpose *ᵥ lockedDualTail y) j := by
  simp [Matrix.mulVec, dotProduct, lockedAuxiliary, lockProgram,
    auxiliary, auxiliaryOriginal, auxiliaryArtificial, lockedDualTail,
    Fin.sum_univ_succ]

/-- A phase-II dual-feasible vector projects to a dual-feasible vector for
the original program. -/
theorem lockedAuxiliary_dualFeasible_to_original (P : StandardLP m n)
    {y : Fin (m + 1) → ℝ} (hy : P.lockedAuxiliary.IsDualFeasible y) :
    P.IsDualFeasible (lockedDualTail y) := by
  constructor
  · intro i
    exact hy.1 i.succ
  · intro j
    have hj := hy.2 (auxiliaryOriginal j)
    rw [P.lockedAuxiliary_dual_mulVec_original y j] at hj
    simpa using hj

/-- Dropping the lock-row coordinate preserves the dual objective. -/
theorem lockedAuxiliary_dualObjective (P : StandardLP m n)
    (y : Fin (m + 1) → ℝ) :
    P.lockedAuxiliary.dualObjective y =
      P.dualObjective (lockedDualTail y) := by
  simp [dualObjective, dotProduct, lockedAuxiliary, lockProgram,
    lockedDualTail, Fin.sum_univ_succ]

end StandardLP
end Chapter29
end CLRS
