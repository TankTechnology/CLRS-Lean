import Mathlib.Tactic

/-!
# Unequal-depth integer branching trees

This datatype records the actual natural-number size and work of every node.
It is intentionally not indexed by a common depth: floor and ceiling branches
may reach the base case at different times.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators

/-- A finite recursion tree whose branches need not have the same height. -/
inductive IntegerBranchingTree (Branch : Type)
  | leaf (size : Nat) (work : Real)
  | node (size : Nat) (work : Real)
      (children : Branch → IntegerBranchingTree Branch)

namespace IntegerBranchingTree

variable {Branch : Type}

/-- Natural-number subproblem size stored at the root. -/
def rootSize : IntegerBranchingTree Branch → Nat
  | .leaf size _ => size
  | .node size _ _ => size

/-- Work stored at the root, whether it is a base or recursive node. -/
def rootWork : IntegerBranchingTree Branch → Real
  | .leaf _ work => work
  | .node _ work _ => work

/-- Work stored in every node of the finite tree. -/
def totalCost [Fintype Branch] : IntegerBranchingTree Branch → Real
  | .leaf _ work => work
  | .node _ work children => work + ∑ branch, totalCost (children branch)

/-- Maximum number of recursive edges on a root-to-leaf path. -/
def height [Fintype Branch] [DecidableEq Branch] :
    IntegerBranchingTree Branch → Nat
  | .leaf _ _ => 0
  | .node _ _ children => 1 + Finset.univ.sup (fun branch => height (children branch))

@[simp] theorem rootSize_leaf (size : Nat) (work : Real) :
    rootSize (.leaf size work : IntegerBranchingTree Branch) = size := rfl

@[simp] theorem rootSize_node (size : Nat) (work : Real)
    (children : Branch → IntegerBranchingTree Branch) :
    rootSize (.node size work children) = size := rfl

@[simp] theorem rootWork_leaf (size : Nat) (work : Real) :
    rootWork (.leaf size work : IntegerBranchingTree Branch) = work := rfl

@[simp] theorem rootWork_node (size : Nat) (work : Real)
    (children : Branch → IntegerBranchingTree Branch) :
    rootWork (.node size work children) = work := rfl

@[simp] theorem totalCost_leaf [Fintype Branch] (size : Nat) (work : Real) :
    totalCost (.leaf size work : IntegerBranchingTree Branch) = work := rfl

@[simp] theorem totalCost_node [Fintype Branch] (size : Nat) (work : Real)
    (children : Branch → IntegerBranchingTree Branch) :
    totalCost (.node size work children) =
      work + ∑ branch, totalCost (children branch) := rfl

@[simp] theorem height_leaf [Fintype Branch] [DecidableEq Branch]
    (size : Nat) (work : Real) :
    height (.leaf size work : IntegerBranchingTree Branch) = 0 := rfl

@[simp] theorem height_node [Fintype Branch] [DecidableEq Branch]
    (size : Nat) (work : Real)
    (children : Branch → IntegerBranchingTree Branch) :
    height (.node size work children) =
      1 + Finset.univ.sup (fun branch => height (children branch)) := rfl

end IntegerBranchingTree

end Chapter04
end CLRS
