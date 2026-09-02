import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Subset
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.SameDepthHeight
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Sorted
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ChildBounded
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Occupancy
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed

/-!
# Chapter 18.3 deletion contract and public-interface checks

The first examples are regression witnesses for contracts that are too strong
for the raw node operation.  Concrete output equalities then cover every
reachable deletion-repair family.  The final `#check` block fixes the bundled,
component-projection, and root-normalized public APIs.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-! ## Counterexample: a minimal non-root leaf is not deletion-ready -/

example : Occupancy 2 false (node [1] []) := by
  simp [Occupancy]

example : ¬ Occupancy 2 false (composedDelete 2 1 (node [1] [])) := by
  simp [composedDelete, sortedRemove, Occupancy]

/-! ## Counterexample: unconditional key subset fails on an empty-key descendant -/

private def subsetBadLeft : BTree :=
  node [1, 2] [node [] []]

private def subsetBadTree : BTree :=
  node [5] [subsetBadLeft, node [9] []]

example : 0 ∈ keysOf (composedDelete 2 5 subsetBadTree) := by
  unfold subsetBadTree
  rw [composedDelete]
  dsimp only
  rw [show findChild [5] 5 = 1 by rfl]
  rw [show [5][1 - 1]? = some 5 by rfl]
  simp only
  rw [show [subsetBadLeft, node [9] []][1 - 1]? = some subsetBadLeft by rfl]
  rw [show [subsetBadLeft, node [9] []][1 - 1 + 1]? = some (node [9] []) by rfl]
  norm_num [numKeys, subsetBadLeft]
  simp [keysOf, maxKey]

example : 0 ∉ keysOf subsetBadTree := by
  simp [subsetBadTree, subsetBadLeft, keysOf]

/-! ## Counterexample: a valid root may require one root-contraction step -/

private def contractionInput : BTree :=
  node [5] [node [1] [], node [9] []]

private lemma contractionInput_wellFormed : WellFormed 2 contractionInput := by
  refine ⟨by simp [contractionInput, Sorted], ?_,
    by simp [contractionInput, Occupancy], ?_⟩
  · unfold contractionInput ChildBounded
    refine ⟨by simp, ?_, ?_⟩
    · intro i hi
      norm_num at hi
      have hi_cases : i = 0 ∨ i = 1 := by omega
      rcases hi_cases with rfl | rfl <;> simp [keysOf]
    · intro child hc
      simp at hc
      rcases hc with rfl | rfl <;> simp [ChildBounded]
  · unfold contractionInput
    refine SameDepth.internal [5] (node [1] []) [node [9] []]
      ?_ (SameDepth.leaf [1]) ?_
    · intro child hc
      simp at hc
      subst child
      simp [heightOf]
    · intro child hc
      simp at hc
      subst child
      exact SameDepth.leaf [9]

private lemma contractionInput_raw :
    composedDelete 2 5 contractionInput = node [] [node [1, 9] []] := by
  unfold contractionInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [5] 5 = 1 by rfl]
  rw [show [5][1 - 1]? = some 5 by rfl]
  simp only
  rw [show [node [1] [], node [9] []][1 - 1]? = some (node [1] []) by rfl]
  rw [show [node [1] [], node [9] []][1 - 1 + 1]? = some (node [9] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

example : ¬ WellFormed 2 (composedDelete 2 5 contractionInput) := by
  rw [contractionInput_raw]
  intro h
  have hocc := h.2.2.1
  simp [Occupancy] at hocc

/-! ## Positive branch regressions -/

private def predecessorInput : BTree :=
  node [10] [node [1, 5] [], node [15] []]

example :
    composedDelete 2 10 predecessorInput =
      node [5] [node [1] [], node [15] []] := by
  unfold predecessorInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [10] 10 = 1 by rfl]
  rw [show [10][1 - 1]? = some 10 by rfl]
  simp only
  rw [show [node [1, 5] [], node [15] []][1 - 1]? =
    some (node [1, 5] []) by rfl]
  rw [show [node [1, 5] [], node [15] []][1 - 1 + 1]? =
    some (node [15] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

private def successorInput : BTree :=
  node [10] [node [1] [], node [15, 20] []]

example :
    composedDelete 2 10 successorInput =
      node [15] [node [1] [], node [20] []] := by
  unfold successorInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [10] 10 = 1 by rfl]
  rw [show [10][1 - 1]? = some 10 by rfl]
  simp only
  rw [show [node [1] [], node [15, 20] []][1 - 1]? =
    some (node [1] []) by rfl]
  rw [show [node [1] [], node [15, 20] []][1 - 1 + 1]? =
    some (node [15, 20] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

example :
    composedDelete 2 5 contractionInput =
      node [] [node [1, 9] []] := by
  exact contractionInput_raw

private def directInput : BTree :=
  node [10] [node [1] [], node [15, 20] []]

example :
    composedDelete 2 20 directInput =
      node [10] [node [1] [], node [15] []] := by
  unfold directInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [10] 20 = 1 by rfl]
  rw [show [10][1 - 1]? = some 10 by rfl]
  simp only
  rw [show [node [1] [], node [15, 20] []][1]? =
    some (node [15, 20] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

private def borrowLeftInput : BTree :=
  node [10] [node [1, 5] [], node [15] []]

example :
    composedDelete 2 15 borrowLeftInput =
      node [5] [node [1] [], node [10] []] := by
  unfold borrowLeftInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [10] 15 = 1 by rfl]
  rw [show [10][1 - 1]? = some 10 by rfl]
  simp only
  rw [show [node [1, 5] [], node [15] []][1]? =
    some (node [15] []) by rfl]
  norm_num [numKeys]
  rw [show [node [1, 5] [], node [15] []][1 - 1]? =
    some (node [1, 5] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

private def borrowRightInput : BTree :=
  node [5] [node [1] [], node [9, 12] []]

example :
    composedDelete 2 1 borrowRightInput =
      node [9] [node [5] [], node [12] []] := by
  unfold borrowRightInput
  rw [composedDelete]
  rw [show [node [1] [], node [9, 12] []].isEmpty = false by rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show findChild [5] 1 = 0 by rfl]
  rw [dif_neg (by omega)]
  rw [show [node [1] [], node [9, 12] []][0]? =
    some (node [1] []) by rfl]
  simp only
  rw [dif_neg (by norm_num [numKeys])]
  rw [show [node [1] [], node [9, 12] []][1]? =
    some (node [9, 12] []) by rfl]
  simp only
  rw [dif_pos (by norm_num [numKeys])]
  rw [show [5][0]? = some 5 by rfl]
  norm_num
  rw [composedDelete]
  simp [sortedRemove]

private def mergeLeftInput : BTree :=
  node [5, 10] [node [1] [], node [7] [], node [12] []]

example :
    composedDelete 2 7 mergeLeftInput =
      node [10] [node [1, 5] [], node [12] []] := by
  unfold mergeLeftInput
  rw [composedDelete]
  dsimp only
  rw [show findChild [5, 10] 7 = 1 by rfl]
  rw [show [5, 10][1 - 1]? = some 5 by rfl]
  simp only
  rw [show [node [1] [], node [7] [], node [12] []][1]? =
    some (node [7] []) by rfl]
  norm_num [numKeys]
  rw [show [node [1] [], node [7] [], node [12] []][1 - 1]? =
    some (node [1] []) by rfl]
  norm_num [numKeys]
  rw [show [node [1] [], node [7] [], node [12] []][1 + 1]? =
    some (node [12] []) by rfl]
  norm_num [numKeys]
  rw [composedDelete]
  simp [sortedRemove]

private def mergeRightInput : BTree :=
  node [5, 10] [node [1] [], node [7] [], node [12] []]

example :
    composedDelete 2 1 mergeRightInput =
      node [10] [node [5, 7] [], node [12] []] := by
  unfold mergeRightInput
  rw [composedDelete]
  rw [show [node [1] [], node [7] [], node [12] []].isEmpty =
    false by rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show findChild [5, 10] 1 = 0 by rfl]
  rw [dif_neg (by omega)]
  rw [show [node [1] [], node [7] [], node [12] []][0]? =
    some (node [1] []) by rfl]
  simp only
  rw [dif_neg (by norm_num [numKeys])]
  rw [show [node [1] [], node [7] [], node [12] []][1]? =
    some (node [7] []) by rfl]
  simp only
  rw [dif_neg (by norm_num [numKeys])]
  rw [show [5, 10][0]? = some 5 by rfl]
  norm_num
  rw [composedDelete]
  simp [sortedRemove]

/-! ## Shape-only single-child fallback and weak component contract -/

private def shapeOnlyInput : BTree :=
  node [] [node [1] []]

private lemma shapeOnlyInput_childBounded :
    ChildBounded shapeOnlyInput := by
  simp [shapeOnlyInput, ChildBounded]

private lemma shapeOnlyInput_sameDepth :
    SameDepth shapeOnlyInput := by
  exact
    SameDepth.internal [] (node [1] []) []
      (by intro child hchild; simp at hchild)
      (SameDepth.leaf [1])
      (by intro child hchild; simp at hchild)

example :
    composedDelete 2 1 shapeOnlyInput =
      node [] [node [] []] := by
  unfold shapeOnlyInput
  rw [composedDelete]
  rw [show [node [1] []].isEmpty = false by rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show findChild [] 1 = 0 by rfl]
  rw [dif_neg (by omega)]
  rw [show [node [1] []][0]? = some (node [1] []) by rfl]
  simp only
  rw [dif_neg (by norm_num [numKeys])]
  rw [show [node [1] []][1]? = none by rfl]
  rw [composedDelete]
  simp [sortedRemove]

example :
    SameDepth (composedDelete 2 1 shapeOnlyInput) ∧
      heightOf (composedDelete 2 1 shapeOnlyInput) =
        heightOf shapeOnlyInput :=
  composedDelete_sameDepth_height 2 1
    shapeOnlyInput_childBounded shapeOnlyInput_sameDepth

/-! ## Corrected bundled and root-normalized interface -/

#check NodeWF
#check DeleteReady
#check KeysSubset
#check RootDeleteResult
#check composedDelete_packet
#check composedDelete_nonRoot_preserves
#check composedDelete_rootResult
#check normalizeRoot
#check normalizeRoot_wellFormed
#check composedDeleteRoot
#check composedDeleteRoot_keys_subset
#check composedDeleteRoot_height
#check composedDeleteRoot_wellFormed
#check keysOf_composedDelete_subset
#check composedDelete_sameDepth_height
#check composedDelete_sorted
#check composedDelete_childBounded
#check composedDelete_occupancy
#check composedDelete_key_bound_lo
#check composedDelete_key_bound_hi

end BTree
end Chapter18
end CLRS
