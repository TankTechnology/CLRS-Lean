import CLRSLean.FourthEdition.Chapter_02.Section_02_2_Analyzing_Algorithms.LineCost.Definitions

/-!
# CLRS Section 2.2 - The complete insertion-sort cost formula

The theorem in this module expands the cost-table evaluator into the seven
terms displayed in the textbook analysis.
-/

namespace CLRS
namespace Chapter02

/--
The complete CLRS insertion-sort running-time equation:

`T(n) = c₁ n + c₂ (n - 1) + c₄ (n - 1) + c₅ Σtᵢ
      + c₆ Σ(tᵢ - 1) + c₇ Σ(tᵢ - 1) + c₈ (n - 1)`.
-/
theorem insertionSortRunningTime_eq_textbook_sum
    (costs : InsertionSortLineCosts) (n : Nat) (t : Nat → Nat) :
    insertionSortRunningTime costs n t =
      costs.c₁ * n +
        costs.c₂ * (n - 1) +
        costs.c₄ * (n - 1) +
        costs.c₅ * insertionSortWhileTestSum n t +
        costs.c₆ * insertionSortBodyIterationSum n t +
        costs.c₇ * insertionSortBodyIterationSum n t +
        costs.c₈ * (n - 1) := by
  rfl

end Chapter02
end CLRS
