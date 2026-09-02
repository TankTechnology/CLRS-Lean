import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree.Execution
import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions.TextbookIdentities

/-!
# The integer tree for `T(n/3) + T(2n/3) + c n`

The larger child uses natural ceiling division.  The generated tree therefore
has no artificial common depth.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators

/-- The textbook rounded size `ceil(2n/3)`. -/
def twoThirdsCeil (n : Nat) : Nat :=
  (2 * n) ⌈/⌉ 3

/-- The smaller floor branch decreases above the chosen cutoff. -/
theorem thirdFloor_lt_self {n : Nat} (hn : 2 < n) : n / 3 < n := by
  exact Nat.div_lt_self (by omega) (by norm_num)

/-- The larger ceiling branch also decreases above the chosen cutoff. -/
theorem twoThirdsCeil_lt_self {n : Nat} (hn : 2 < n) : twoThirdsCeil n < n := by
  rw [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div]
  omega

/-- Floor and ceiling differ by at most one for the two-thirds child. -/
theorem twoThirds_floor_ceil_sandwich (n : Nat) :
    (2 * n) / 3 ≤ twoThirdsCeil n ∧
      twoThirdsCeil n ≤ (2 * n) / 3 + 1 := by
  constructor
  · rw [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div]
    omega
  · rw [twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div]
    omega

/-- Two differently rounded children, with base cases through size two. -/
def unbalancedIntegerSpec (c base : Real) : IntegerBranchingSpec Bool where
  cutoff := 2
  childSize := fun branch n => if branch then twoThirdsCeil n else n / 3
  localCost := fun n => c * (n : Real)
  baseCost := fun _ => base
  decreases := by
    intro branch n hn
    cases branch with
    | false =>
        simpa using thirdFloor_lt_self hn
    | true =>
        simpa using twoThirdsCeil_lt_self hn

/-- Independent textbook equations for the rounded unbalanced recurrence. -/
structure UnbalancedIntegerRecurrence (c base : Real) (T : Nat → Real) : Prop where
  base_eq : ∀ n, n ≤ 2 → T n = base
  step_eq : ∀ n, 2 < n →
    T n = T (n / 3) + T (twoThirdsCeil n) + c * (n : Real)

/-- The textbook equations instantiate the generic finite-tree semantics. -/
theorem UnbalancedIntegerRecurrence.satisfies {c base : Real} {T : Nat → Real}
    (hT : UnbalancedIntegerRecurrence c base T) :
    (unbalancedIntegerSpec c base).Satisfies T := by
  constructor
  · intro n hn
    exact hT.base_eq n hn
  · intro n hn
    rw [hT.step_eq n hn]
    simp [unbalancedIntegerSpec]
    ring

/-- Exact equality between the rounded recurrence and its explicit tree. -/
theorem unbalancedIntegerTree_totalCost_eq {c base : Real} {T : Nat → Real}
    (hT : UnbalancedIntegerRecurrence c base T) (n : Nat) :
    IntegerBranchingTree.totalCost ((unbalancedIntegerSpec c base).build n) = T n :=
  IntegerBranchingSpec.build_totalCost_eq _ _ hT.satisfies n

/-- Cost function computed by the generated unbalanced integer tree. -/
def unbalancedIntegerCost (c base : Real) (n : Nat) : Real :=
  IntegerBranchingTree.totalCost ((unbalancedIntegerSpec c base).build n)

@[simp] theorem unbalancedIntegerCost_base {c base : Real} {n : Nat}
    (hn : n ≤ 2) : unbalancedIntegerCost c base n = base := by
  simp [unbalancedIntegerCost, unbalancedIntegerSpec, hn]

theorem unbalancedIntegerCost_step {c base : Real} {n : Nat}
    (hn : 2 < n) :
    unbalancedIntegerCost c base n =
      unbalancedIntegerCost c base (n / 3) +
        unbalancedIntegerCost c base (twoThirdsCeil n) + c * (n : Real) := by
  rw [unbalancedIntegerCost, IntegerBranchingSpec.build_of_lt _ _ hn]
  simp only [IntegerBranchingTree.totalCost_node]
  simp [unbalancedIntegerSpec, unbalancedIntegerCost]
  ring

theorem unbalancedIntegerCost_satisfies (c base : Real) :
    UnbalancedIntegerRecurrence c base (unbalancedIntegerCost c base) := by
  constructor
  · intro n hn
    exact unbalancedIntegerCost_base hn
  · intro n hn
    exact unbalancedIntegerCost_step hn

/--
At input four, the {lit}`floor(4/3)` child is already a leaf while the
{lit}`ceil(8/3)` child expands once more.  This witnesses genuinely unequal depth.
-/
theorem unbalancedIntegerTree_has_unequal_depth :
    IntegerBranchingTree.height
        ((unbalancedIntegerSpec 1 1).build
          ((unbalancedIntegerSpec 1 1).childSize false 4)) ≠
      IntegerBranchingTree.height
        ((unbalancedIntegerSpec 1 1).build
          ((unbalancedIntegerSpec 1 1).childSize true 4)) := by
  have hleft : (unbalancedIntegerSpec 1 1).childSize false 4 = 1 := by
    norm_num [unbalancedIntegerSpec]
  have hright : (unbalancedIntegerSpec 1 1).childSize true 4 = 3 := by
    norm_num [unbalancedIntegerSpec, twoThirdsCeil, Nat.ceilDiv_eq_add_pred_div]
  rw [hleft, hright]
  have hheightOne : IntegerBranchingTree.height
      ((unbalancedIntegerSpec 1 1).build 1) = 0 := by
    rw [IntegerBranchingSpec.build_of_le _ _ (by norm_num [unbalancedIntegerSpec])]
    rfl
  have hheightThree : IntegerBranchingTree.height
      ((unbalancedIntegerSpec 1 1).build 3) = 1 := by
    rw [IntegerBranchingSpec.build_of_lt _ _ (by norm_num [unbalancedIntegerSpec])]
    simp [IntegerBranchingTree.height, unbalancedIntegerSpec, twoThirdsCeil]
  omega

/-- The limiting one-third and two-thirds branch weights sum to one. -/
theorem unbalancedInteger_characteristic_one :
    (1 : Real) / 3 + 2 / 3 = 1 := by
  norm_num

end Chapter04
end CLRS
