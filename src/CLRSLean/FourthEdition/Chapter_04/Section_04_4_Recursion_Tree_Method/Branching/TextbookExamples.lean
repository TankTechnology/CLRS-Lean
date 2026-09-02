import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.LevelSums

/-!
# Textbook branching-recursion-tree examples

The theorems below are exact fixed-depth expansions over real-valued problem
scales.  They formalize the level-cost calculations from CLRS §4.4 while
keeping the assumptions visible:

- no floor or ceiling is taken at a child size;
- all branches are expanded through a common cutoff depth;
- `leafWork` is the common cost assigned at that cutoff.

Consequently these results are the recursion-tree algebra for the original
branch ratios, not an arbitrary-input termination theorem.  A transfer from
these exact scales to rounded natural-number recurrences needs separate
monotonicity and floor/ceiling bounds.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators
open BranchingRecursionTree

/-! ## The balanced example `3T(n/4) + c n^2` -/

/-- The fixed-depth recursion tree for `3T(n/4) + c n^2`.  Quadratic local
work scales by `1/16` on each of the three child branches. -/
noncomputable def balancedThreeQuarterTree (c n leafWork : Real) (depth : Nat) :
    BranchingRecursionTree (Fin 3) depth :=
  scaledBranchingTree (fun _ : Fin 3 => (1 : Real) / 16) (c * n ^ 2) leafWork depth

/-- At level `k`, the balanced example costs exactly
`c n^2 (3/16)^k`. -/
theorem balancedThreeQuarter_levelCost (c n leafWork : Real) {depth : Nat}
    (level : Fin depth) :
    levelCost (balancedThreeQuarterTree c n leafWork depth) level =
      c * n ^ 2 * ((3 : Real) / 16) ^ level.val := by
  rw [balancedThreeQuarterTree, scaledBranchingTree_levelCost]
  norm_num

/-- Exact internal-level plus leaf decomposition for the balanced example. -/
theorem balancedThreeQuarter_totalCost_eq (c n leafWork : Real) (depth : Nat) :
    totalCost (balancedThreeQuarterTree c n leafWork depth) =
      (∑ level : Fin depth,
        c * n ^ 2 * ((3 : Real) / 16) ^ level.val) +
      (3 : Real) ^ depth * leafWork := by
  rw [balancedThreeQuarterTree, scaledBranchingTree_totalCost]
  norm_num

/-- The internal work of `3T(n/4) + c n^2` is bounded by the convergent
geometric sum `16/13 * c n^2`; the leaf contribution remains explicit. -/
theorem balancedThreeQuarter_totalCost_le (c n leafWork : Real)
    (hc : 0 <= c) (depth : Nat) :
    totalCost (balancedThreeQuarterTree c n leafWork depth) <=
      ((16 : Real) / 13) * (c * n ^ 2) + (3 : Real) ^ depth * leafWork := by
  have hbase : 0 <= c * n ^ 2 := mul_nonneg hc (sq_nonneg n)
  have hlevels := geometricLevelSum_le (c * n ^ 2) ((3 : Real) / 16)
    hbase (by norm_num) (by norm_num) depth
  have hlevelsFin :
      (∑ level : Fin depth, c * n ^ 2 * ((3 : Real) / 16) ^ level.val) <=
        (c * n ^ 2) / (1 - (3 : Real) / 16) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun level : Nat => c * n ^ 2 * ((3 : Real) / 16) ^ level) depth]
    exact hlevels
  rw [balancedThreeQuarter_totalCost_eq]
  calc
    (∑ level : Fin depth, c * n ^ 2 * ((3 : Real) / 16) ^ level.val) +
          (3 : Real) ^ depth * leafWork <=
        (c * n ^ 2) / (1 - (3 : Real) / 16) +
          (3 : Real) ^ depth * leafWork := add_le_add hlevelsFin le_rfl
    _ = ((16 : Real) / 13) * (c * n ^ 2) +
          (3 : Real) ^ depth * leafWork := by ring

/-! ## The unbalanced example `T(n/3) + T(2n/3) + c n` -/

/-- The two exact child-work ratios for the linear-work unbalanced recurrence. -/
noncomputable def thirdTwoThirdRatio : Bool -> Real
  | false => (1 : Real) / 3
  | true => (2 : Real) / 3

/-- A common-depth expansion of `T(n/3) + T(2n/3) + c n`.

The two child trees retain their different `1/3` and `2/3` scales; they are not
replaced by a balanced recurrence. -/
noncomputable def unbalancedThirdTwoThirdTree (c n leafWork : Real) (depth : Nat) :
    BranchingRecursionTree Bool depth :=
  scaledBranchingTree thirdTwoThirdRatio (c * n) leafWork depth

/-- Since `1/3 + 2/3 = 1`, every internal level in the common-depth expansion
has exactly the root's linear work `c n`. -/
theorem unbalancedThirdTwoThird_levelCost (c n leafWork : Real) {depth : Nat}
    (level : Fin depth) :
    levelCost (unbalancedThirdTwoThirdTree c n leafWork depth) level = c * n := by
  rw [unbalancedThirdTwoThirdTree, scaledBranchingTree_levelCost]
  have hratio : (∑ branch : Bool, thirdTwoThirdRatio branch) = (1 : Real) := by
    norm_num [thirdTwoThirdRatio]
  rw [hratio, one_pow, mul_one]

/-- Exact total cost through a common cutoff depth: `depth * c n` internal
work plus one `leafWork` contribution for each of the `2^depth` leaves.

This theorem is deliberately not advertised as an arbitrary-size solution:
the actual `1/3` and `2/3` branches reach a natural-number base threshold at
different depths after rounding. -/
theorem unbalancedThirdTwoThird_totalCost (c n leafWork : Real) (depth : Nat) :
    totalCost (unbalancedThirdTwoThirdTree c n leafWork depth) =
      (depth : Real) * (c * n) + (2 : Real) ^ depth * leafWork := by
  rw [unbalancedThirdTwoThirdTree, scaledBranchingTree_totalCost]
  have hratio : (∑ branch : Bool, thirdTwoThirdRatio branch) = (1 : Real) := by
    norm_num [thirdTwoThirdRatio]
  rw [hratio]
  simp [nsmul_eq_mul]

end Chapter04
end CLRS
