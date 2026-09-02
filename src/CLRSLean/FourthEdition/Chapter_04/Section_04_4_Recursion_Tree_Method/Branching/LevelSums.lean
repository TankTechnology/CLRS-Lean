import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.Model

/-!
# Reusable branching level sums

This file builds a full recursion tree from per-branch work-scaling ratios and
proves its exact per-level cost.  It also packages the convergent geometric
sum bound used by the balanced textbook example.
-/

namespace CLRS
namespace Chapter04

open Finset
open scoped BigOperators
open BranchingRecursionTree

variable {Branch : Type} [Fintype Branch]

/-- A homogeneous branching expansion.  A child on branch `branch` receives
`ratios branch` times its parent's local work.  Leaves have a common cutoff
cost; this parameter is intentionally separate from the internal work scale. -/
def scaledBranchingTree (ratios : Branch -> Real) (rootWork leafWork : Real) :
    (depth : Nat) -> BranchingRecursionTree Branch depth
  | 0 => .leaf leafWork
  | depth + 1 => .node rootWork (fun branch =>
      scaledBranchingTree ratios (rootWork * ratios branch) leafWork depth)

/-- At level `k`, the total work is the root work times the `k`th power of the
sum of the per-branch work ratios. -/
theorem scaledBranchingTree_levelCost (ratios : Branch -> Real)
    (rootWork leafWork : Real) {depth : Nat} (level : Fin depth) :
    levelCost (scaledBranchingTree ratios rootWork leafWork depth) level =
      rootWork * (∑ branch, ratios branch) ^ level.val := by
  induction depth generalizing rootWork with
  | zero => exact Fin.elim0 level
  | succ depth ih =>
      refine Fin.cases ?_ (fun childLevel => ?_) level
      · simp [scaledBranchingTree, levelCost]
      · simp only [scaledBranchingTree, levelCost, Fin.cases_succ]
        simp_rw [ih]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        simp only [Fin.val_succ, pow_succ]
        ring

/-- A full depth-`d` expansion has `card Branch ^ d` leaves. -/
theorem scaledBranchingTree_leafCost (ratios : Branch -> Real)
    (rootWork leafWork : Real) (depth : Nat) :
    leafCost (scaledBranchingTree ratios rootWork leafWork depth) =
      (Fintype.card Branch : Real) ^ depth * leafWork := by
  induction depth generalizing rootWork with
  | zero => simp [scaledBranchingTree, leafCost]
  | succ depth ih =>
      simp [scaledBranchingTree, leafCost, ih, Finset.sum_const, nsmul_eq_mul,
        pow_succ]
      ring

/-- Exact closed form of the full branching expansion through a fixed depth. -/
theorem scaledBranchingTree_totalCost (ratios : Branch -> Real)
    (rootWork leafWork : Real) (depth : Nat) :
    totalCost (scaledBranchingTree ratios rootWork leafWork depth) =
      (∑ level : Fin depth,
        rootWork * (∑ branch, ratios branch) ^ level.val) +
      (Fintype.card Branch : Real) ^ depth * leafWork := by
  rw [totalCost_eq_levelCosts_add_leafCost]
  simp_rw [scaledBranchingTree_levelCost]
  rw [scaledBranchingTree_leafCost]

/-- A reusable finite geometric level-sum bound. -/
theorem geometricLevelSum_le (base ratio : Real) (hbase : 0 <= base)
    (hratio_nonneg : 0 <= ratio) (hratio_lt_one : ratio < 1) (depth : Nat) :
    (∑ level ∈ Finset.range depth, base * ratio ^ level) <=
      base / (1 - ratio) := by
  have hsumm : Summable fun level : Nat => ratio ^ level :=
    summable_geometric_of_lt_one hratio_nonneg hratio_lt_one
  have hpartial : (∑ level ∈ Finset.range depth, ratio ^ level) <=
      (1 - ratio)⁻¹ := by
    calc
      (∑ level ∈ Finset.range depth, ratio ^ level) <= ∑' level : Nat, ratio ^ level :=
        hsumm.sum_le_tsum (Finset.range depth)
          (fun level _ => pow_nonneg hratio_nonneg level)
      _ = (1 - ratio)⁻¹ :=
        tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one
  calc
    (∑ level ∈ Finset.range depth, base * ratio ^ level) =
        base * ∑ level ∈ Finset.range depth, ratio ^ level := by
      rw [Finset.mul_sum]
    _ <= base * (1 - ratio)⁻¹ := mul_le_mul_of_nonneg_left hpartial hbase
    _ = base / (1 - ratio) := by rw [div_eq_mul_inv]

end Chapter04
end CLRS
