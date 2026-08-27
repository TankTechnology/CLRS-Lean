import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Basic

/-!
# CLRS Section 28.1 - Executable pivot scan

Soundness, failure characterization, and comparison work for the concrete
first-column scan.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Zero F] [DecidableEq F]

theorem findPivotListWithCost_eq_none {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (ps : List (Fin (n + 1))) :
    (findPivotListWithCost A ps).pivot = none ↔
      ∀ p ∈ ps, A p 0 = 0 := by
  induction ps with
  | nil => simp [findPivotListWithCost]
  | cons q qs ih =>
      by_cases hq : A q 0 = 0
      · simp [findPivotListWithCost, hq, ih]
      · simp [findPivotListWithCost, hq]

theorem findPivotListWithCost_comparisons_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (ps : List (Fin (n + 1))) :
    (findPivotListWithCost A ps).comparisons ≤ ps.length := by
  induction ps with
  | nil => simp [findPivotListWithCost]
  | cons q qs ih =>
      by_cases hq : A q 0 = 0
      · simp [findPivotListWithCost, hq]
        omega
      · simp [findPivotListWithCost, hq]

/-- A returned pivot is a genuinely nonzero first-column entry. -/
theorem findPivotWithCost_found {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    {p : {p : Fin (n + 1) // A p 0 ≠ 0}}
    (_hp : (findPivotWithCost A).pivot = some p) : A p.1 0 ≠ 0 :=
  p.2

/-- The pivot scan fails exactly when the complete first column is zero. -/
theorem findPivotWithCost_eq_none {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    (findPivotWithCost A).pivot = none ↔ ∀ p : Fin (n + 1), A p 0 = 0 := by
  rw [findPivotWithCost, findPivotListWithCost_eq_none]
  constructor
  · intro h p
    exact h p (List.mem_finRange p)
  · intro h p _hp
    exact h p

/-- At most one pivot comparison is charged per row. -/
theorem findPivotWithCost_comparisons_le {n : Nat}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    (findPivotWithCost A).comparisons ≤ n + 1 := by
  simpa [findPivotWithCost] using
    findPivotListWithCost_comparisons_le A (List.finRange (n + 1))

end Chapter28
end CLRS
