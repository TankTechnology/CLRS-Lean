import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Execution
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input

/-!
# The integer tree for `3T(n/4) + c n²`

This is the rounded, arbitrary-input counterpart of the existing fixed-depth
real-scale level calculation.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators

/-- Three equal floor-divided children, with base cases at sizes zero and one. -/
def balancedIntegerSpec (c base : Real) : IntegerBranchingSpec (Fin 3) where
  cutoff := 1
  childSize := fun _ n => n / 4
  localCost := fun n => c * (n : Real) ^ 2
  baseCost := fun _ => base
  decreases := by
    intro _ n hn
    exact Nat.div_lt_self (by omega) (by norm_num)

/-- Independent textbook equations for the rounded balanced recurrence. -/
structure BalancedIntegerRecurrence (c base : Real) (T : Nat → Real) : Prop where
  base_eq : ∀ n, n ≤ 1 → T n = base
  step_eq : ∀ n, 1 < n →
    T n = 3 * T (n / 4) + c * (n : Real) ^ 2

/-- The textbook equations instantiate the generic finite-tree semantics. -/
theorem BalancedIntegerRecurrence.satisfies {c base : Real} {T : Nat → Real}
    (hT : BalancedIntegerRecurrence c base T) :
    (balancedIntegerSpec c base).Satisfies T := by
  constructor
  · intro n hn
    exact hT.base_eq n hn
  · intro n hn
    rw [hT.step_eq n hn]
    simp [balancedIntegerSpec]
    ring

/-- Exact equality between the rounded recurrence and its explicit tree. -/
theorem balancedIntegerTree_totalCost_eq {c base : Real} {T : Nat → Real}
    (hT : BalancedIntegerRecurrence c base T) (n : Nat) :
    IntegerBranchingTree.totalCost ((balancedIntegerSpec c base).build n) = T n :=
  IntegerBranchingSpec.build_totalCost_eq _ _ hT.satisfies n

/-- Cost function computed by the generated balanced integer tree. -/
def balancedIntegerCost (c base : Real) (n : Nat) : Real :=
  IntegerBranchingTree.totalCost ((balancedIntegerSpec c base).build n)

@[simp] theorem balancedIntegerCost_base {c base : Real} {n : Nat}
    (hn : n ≤ 1) : balancedIntegerCost c base n = base := by
  simp [balancedIntegerCost, balancedIntegerSpec, hn]

theorem balancedIntegerCost_step {c base : Real} {n : Nat}
    (hn : 1 < n) :
    balancedIntegerCost c base n =
      3 * balancedIntegerCost c base (n / 4) + c * (n : Real) ^ 2 := by
  rw [balancedIntegerCost, IntegerBranchingSpec.build_of_lt _ _ hn]
  simp only [IntegerBranchingTree.totalCost_node]
  simp [balancedIntegerSpec, balancedIntegerCost]
  ring

theorem balancedIntegerCost_satisfies (c base : Real) :
    BalancedIntegerRecurrence c base (balancedIntegerCost c base) := by
  constructor
  · intro n hn
    exact balancedIntegerCost_base hn
  · intro n hn
    exact balancedIntegerCost_step hn

/--
Forcing term that makes the generated tree cost an all-input floor recurrence,
including the explicitly represented base cases.
-/
def balancedIntegerForcing (c base : Real) (n : Nat) : Real :=
  balancedIntegerCost c base n - 3 * balancedIntegerCost c base (n / 4)

/-- Direct connection from the explicit tree to the all-input §4.6 interface. -/
theorem balancedIntegerCost_floorRecurrence (c base : Real) :
    FloorDivideRecurrence 3 4 (balancedIntegerForcing c base)
      (balancedIntegerCost c base) := by
  constructor
  intro n
  simp [balancedIntegerForcing]

/-- Above the cutoff, the all-input forcing is exactly the textbook `c n²`. -/
theorem balancedIntegerForcing_of_lt {c base : Real} {n : Nat} (hn : 1 < n) :
    balancedIntegerForcing c base n = c * (n : Real) ^ 2 := by
  rw [balancedIntegerForcing, balancedIntegerCost_step hn]
  ring

end Chapter04
end CLRS
