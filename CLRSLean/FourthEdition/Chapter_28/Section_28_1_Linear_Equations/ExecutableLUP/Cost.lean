import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Correctness

/-!
# CLRS Section 28.1 - Executable LUP work

The cubic bound is derived from the counter stored by the recursive execution,
including pivot comparisons, pointwise elimination, successful factor
assembly, and both successful and early-failure paths.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Field F] [DecidableEq F]

private theorem lup_step_arithmetic (n : Nat) :
    (n + 1) + 3 * (n + 1) ^ 2 + 4 * n ^ 3 + n ≤ 4 * (n + 1) ^ 3 := by
  nlinarith [sq_nonneg (n : Int)]

/-- Every execution path uses at most `4n³` pivot comparisons and field
operations in the declared exact-algebra unit-cost model. -/
theorem lupDecomposeWithCost_work_le : ∀ {n : Nat}
    (A : Matrix (Fin n) (Fin n) F),
    (lupDecomposeWithCost n A).work ≤ 4 * n ^ 3
  | 0, _A => by simp [lupDecomposeWithCost]
  | n + 1, A => by
      have hpivotWork := findPivotWithCost_comparisons_le A
      cases hpivot : (findPivotWithCost A).pivot with
      | none =>
          have hwork : (lupDecomposeWithCost (n + 1) A).work =
              (findPivotWithCost A).comparisons := by
            simp [lupDecomposeWithCost, hpivot]
          rw [hwork]
          have hone : n + 1 ≤ 4 * (n + 1) ^ 3 := by
            nlinarith [sq_nonneg (n : Int)]
          exact le_trans hpivotWork hone
      | some p =>
          let B := pivotedMatrix A p.1
          have hB0 : B 0 0 ≠ 0 := by
            simpa [B, pivotedMatrix] using p.2
          let eliminated := eliminateWithCost B hB0
          let M : Matrix (Fin n) (Fin n) F :=
            fun i j => eliminated.value (Fin.succ i) (Fin.succ j)
          let child := lupDecomposeWithCost n M
          have helimWork : eliminated.work ≤ 3 * (n + 1) ^ 2 := by
            simpa [eliminated] using eliminateWithCost_work_le B hB0
          have hchildWork : child.work ≤ 4 * n ^ 3 := by
            simpa [child] using lupDecomposeWithCost_work_le M
          have hsum :
              (findPivotWithCost A).comparisons + eliminated.work + child.work + n ≤
                (n + 1) + 3 * (n + 1) ^ 2 + 4 * n ^ 3 + n := by
            omega
          have hwork : (lupDecomposeWithCost (n + 1) A).work ≤
              (findPivotWithCost A).comparisons + eliminated.work + child.work + n := by
            cases hchild : child.result <;>
              simp [lupDecomposeWithCost, hpivot, B, eliminated, M, child, hchild]
          exact hwork.trans (hsum.trans (lup_step_arithmetic n))

/-- Public executable Theorem 28.1 bundle: one run returns certified LUP
factors and satisfies the cubic work bound. -/
theorem lupDecomposeWithCost_correct {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ factors,
      (lupDecomposeWithCost n A).result = some factors ∧
      IsUnitLowerTriangular factors.lower ∧
      IsUpperTriangular factors.upper ∧
      (∀ i : Fin n, factors.upper i i ≠ 0) ∧
      factors.perm.permMatrix F * A = factors.lower * factors.upper ∧
      (lupDecomposeWithCost n A).work ≤ 4 * n ^ 3 := by
  obtain ⟨factors, hresult⟩ := lupDecomposeWithCost_nonsingular A hA
  have hcorrect := lupDecomposeWithCost_sound A factors hresult
  exact ⟨factors, hresult, hcorrect.1, hcorrect.2.1,
    lupDecomposeWithCost_upper_diag_ne_zero A factors hresult, hcorrect.2.2,
    lupDecomposeWithCost_work_le A⟩

end Chapter28
end CLRS
