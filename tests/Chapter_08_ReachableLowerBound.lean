import CLRSLean.FourthEdition.Chapter_08
open CLRS.Chapter08
#check SortTree.runWithCost_result
#check comparisonSort_exists_run_lowerBound

-- A self-comparison makes the deeper right subtree unreachable.
private def unreachableTree : SortTree 1 :=
  .node 0 0 (.leaf 1) (.node 0 0 (.leaf 1) (.node 0 0 (.leaf 1) (.leaf 1)))

example : unreachableTree.height = 3 := by decide
example (π : Equiv.Perm (Fin 1)) : (unreachableTree.runWithCost π).2 = 1 := by
  simp [unreachableTree, SortTree.runWithCost]

example : CorrectSort unreachableTree := by
  intro π
  simp only [unreachableTree, SortTree.run, le_refl, if_true]
  congr 1
  exact Subsingleton.elim _ _

-- No reachability assumptions on all syntactic branches are necessary.
example (n : Nat) (hn : 2 ≤ n) (T : SortTree n) (hT : CorrectSort T) :
    ∃ π, ((n : ℝ) / 2) * Real.logb 2 (n : ℝ) ≤ ((T.runWithCost π).2 : ℝ) :=
  comparisonSort_exists_run_lowerBound n hn hT

-- The factorial interface also handles the empty permutation type's single input.
example (T : SortTree 0) (hT : CorrectSort T) :
    ∃ π, Real.logb 2 ((0 : Nat).factorial : ℝ) ≤ ((T.runWithCost π).2 : ℝ) :=
  comparisonSort_exists_run_log_factorial hT
