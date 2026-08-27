import Mathlib.Tactic

/-!
# Full branching recursion trees

`BranchingRecursionTree Branch depth` is an explicit, finite expansion of a
branching recurrence through exactly `depth` internal levels.  Every internal
node has one child for each value of the finite type `Branch`; all leaves lie
at the same cutoff depth.  This is the exact-power / fixed-depth model used in
the textbook level-cost calculation.  Floor and ceiling transfer for arbitrary
input sizes is deliberately a separate concern.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators

/-- A full finite branching recursion tree with `depth` internal levels. -/
inductive BranchingRecursionTree (Branch : Type) : Nat -> Type
  | leaf (cost : Real) : BranchingRecursionTree Branch 0
  | node {depth : Nat} (work : Real)
      (children : Branch -> BranchingRecursionTree Branch depth) :
      BranchingRecursionTree Branch (depth + 1)

namespace BranchingRecursionTree

variable {Branch : Type} [Fintype Branch]

/-- Total work stored in all internal nodes and leaves. -/
def totalCost : {depth : Nat} -> BranchingRecursionTree Branch depth -> Real
  | 0, .leaf cost => cost
  | _ + 1, .node work children => work + ∑ branch, totalCost (children branch)

/-- Total contribution of the leaves at the cutoff depth. -/
def leafCost : {depth : Nat} -> BranchingRecursionTree Branch depth -> Real
  | 0, .leaf cost => cost
  | _ + 1, .node _ children => ∑ branch, leafCost (children branch)

/-- Work contributed by the internal nodes at one depth. -/
def levelCost : {depth : Nat} -> (tree : BranchingRecursionTree Branch depth) ->
    Fin depth -> Real
  | 0, .leaf _, level => Fin.elim0 level
  | _ + 1, .node work children, level =>
      Fin.cases work (fun childLevel =>
        ∑ branch, levelCost (children branch) childLevel) level

/-- Exact recursion-tree decomposition: total cost is the sum of all internal
level costs plus the cost of the leaves at the common cutoff depth. -/
theorem totalCost_eq_levelCosts_add_leafCost {depth : Nat}
    (tree : BranchingRecursionTree Branch depth) :
    totalCost tree = (∑ level : Fin depth, levelCost tree level) + leafCost tree := by
  induction tree with
  | leaf cost => simp [totalCost, leafCost]
  | @node depth work children ih =>
      simp only [totalCost, leafCost]
      rw [Fin.sum_univ_succ]
      simp only [levelCost, Fin.cases_zero, Fin.cases_succ]
      simp_rw [ih]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      ring

end BranchingRecursionTree

end Chapter04
end CLRS
