import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.Execution
import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees

/-!
# From executable quicksort to binary-search-tree depth

This module proves the operational half of the randomized-quicksort bridge.
For a duplicate-free input, the recursive comparison counter is exactly the
sum of the search depths in the binary search tree obtained by inserting the
same keys in input order.
-/

namespace CLRS
namespace Chapter07

/-- Sum of the search depths of the keys in `xs` within `t`. -/
def bstDepthSumOn (xs : List Nat) (t : Chapter12.BSTree) : Nat :=
  (xs.map (fun x => Chapter12.BSTree.depth x t)).sum

/-- On a duplicate-free pivot call, quicksort's `≤ pivot` left partition is
the BST construction's strict `< pivot` partition. -/
theorem partitionAround_left_eq_filter_lt_of_nodup
    (pivot : Nat) (tail : List Nat) (h : (pivot :: tail).Nodup) :
    (partitionAround pivot tail).1 =
      tail.filter (fun x => decide (x < pivot)) := by
  rw [partitionAround_left_eq_filter]
  apply List.filter_congr
  intro x hx
  have hne : x ≠ pivot := by
    intro hxp
    subst x
    exact (List.nodup_cons.mp h).1 hx
  simp only [decide_eq_decide]
  omega

private theorem bstDepthSumOn_node_left
    (xs : List Nat) (left right : Chapter12.BSTree) (pivot : Nat)
    (hall : ∀ x ∈ xs, x < pivot) :
    bstDepthSumOn xs (.node left pivot right) =
      xs.length + bstDepthSumOn xs left := by
  induction xs with
  | nil => simp [bstDepthSumOn]
  | cons x xs ih =>
      have hx : x < pivot := hall x (by simp)
      have hne : x ≠ pivot := Nat.ne_of_lt hx
      have hrest : ∀ y ∈ xs, y < pivot := by
        intro y hy
        exact hall y (by simp [hy])
      change Chapter12.BSTree.depth x (.node left pivot right) +
          bstDepthSumOn xs (.node left pivot right) =
        (x :: xs).length + bstDepthSumOn (x :: xs) left
      simp only [Chapter12.BSTree.depth, hne, hx, if_false, if_true]
      rw [ih hrest]
      simp only [List.length_cons, bstDepthSumOn, List.map_cons, List.sum_cons]
      omega

private theorem bstDepthSumOn_node_right
    (xs : List Nat) (left right : Chapter12.BSTree) (pivot : Nat)
    (hall : ∀ x ∈ xs, pivot < x) :
    bstDepthSumOn xs (.node left pivot right) =
      xs.length + bstDepthSumOn xs right := by
  induction xs with
  | nil => simp [bstDepthSumOn]
  | cons x xs ih =>
      have hx : pivot < x := hall x (by simp)
      have hne : x ≠ pivot := Nat.ne_of_gt hx
      have hnlt : ¬x < pivot := Nat.not_lt_of_ge (Nat.le_of_lt hx)
      have hrest : ∀ y ∈ xs, pivot < y := by
        intro y hy
        exact hall y (by simp [hy])
      change Chapter12.BSTree.depth x (.node left pivot right) +
          bstDepthSumOn xs (.node left pivot right) =
        (x :: xs).length + bstDepthSumOn (x :: xs) right
      simp only [Chapter12.BSTree.depth, hne, hnlt, if_false]
      rw [ih hrest]
      simp only [List.length_cons, bstDepthSumOn, List.map_cons, List.sum_cons]
      omega

/-- The recursive comparison counter and the BST depth sum satisfy the same
recurrence on every duplicate-free input whose length is covered by `fuel`. -/
theorem quickSortComparisonsFuel_eq_bstDepthSumOn
    (fuel : Nat) (xs : List Nat) (hlen : xs.length ≤ fuel)
    (hnodup : xs.Nodup) :
    quickSortComparisonsFuel fuel xs =
      bstDepthSumOn xs (Chapter12.BSTree.buildFromList xs) := by
  induction fuel generalizing xs with
  | zero =>
      have hnil : xs = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst xs
      simp [quickSortComparisonsFuel, bstDepthSumOn, Chapter12.BSTree.buildFromList]
  | succ fuel ih =>
      cases xs with
      | nil =>
          simp [quickSortComparisonsFuel, bstDepthSumOn, Chapter12.BSTree.buildFromList]
      | cons pivot tail =>
          let left := tail.filter (fun x => decide (x < pivot))
          let right := tail.filter (fun x => decide (pivot < x))
          have htailLength : tail.length ≤ fuel := by
            exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
          have htailNodup : tail.Nodup := hnodup.tail
          have hleft : (partitionAround pivot tail).1 = left := by
            simpa [left] using
              partitionAround_left_eq_filter_lt_of_nodup pivot tail hnodup
          have hright : (partitionAround pivot tail).2 = right := by
            simpa [right] using partitionAround_right_eq_filter pivot tail
          have hleftLength : left.length ≤ fuel :=
            Nat.le_trans (List.length_filter_le _ _) htailLength
          have hrightLength : right.length ≤ fuel :=
            Nat.le_trans (List.length_filter_le _ _) htailLength
          have hleftNodup : left.Nodup := htailNodup.filter _
          have hrightNodup : right.Nodup := htailNodup.filter _
          have ihLeft := ih left hleftLength hleftNodup
          have ihRight := ih right hrightLength hrightNodup
          have hperm : (left ++ right).Perm tail := by
            simpa [hleft, hright] using partitionAround_perm pivot tail
          let leftTree := Chapter12.BSTree.buildFromList left
          let rightTree := Chapter12.BSTree.buildFromList right
          have hsplit :
              bstDepthSumOn tail (.node leftTree pivot rightTree) =
                bstDepthSumOn left (.node leftTree pivot rightTree) +
                  bstDepthSumOn right (.node leftTree pivot rightTree) := by
            have hsum :=
              (hperm.map (fun x => Chapter12.BSTree.depth x
                (.node leftTree pivot rightTree))).sum_eq
            simpa [bstDepthSumOn, List.map_append] using hsum.symm
          have hallLeft : ∀ x ∈ left, x < pivot := by
            intro x hx
            exact of_decide_eq_true (List.mem_filter.mp hx).2
          have hallRight : ∀ x ∈ right, pivot < x := by
            intro x hx
            exact of_decide_eq_true (List.mem_filter.mp hx).2
          have hleftDepth :=
            bstDepthSumOn_node_left left leftTree rightTree pivot hallLeft
          have hrightDepth :=
            bstDepthSumOn_node_right right leftTree rightTree pivot hallRight
          have hpartsLength : left.length + right.length = tail.length := by
            simpa [hleft, hright] using partitionAround_length_add pivot tail
          have hdepthRec :
              bstDepthSumOn (pivot :: tail)
                  (Chapter12.BSTree.buildFromList (pivot :: tail)) =
                tail.length + bstDepthSumOn left leftTree +
                  bstDepthSumOn right rightTree := by
            rw [Chapter12.BSTree.buildFromList_cons]
            change bstDepthSumOn (pivot :: tail)
                (.node leftTree pivot rightTree) = _
            rw [show bstDepthSumOn (pivot :: tail)
                (.node leftTree pivot rightTree) =
                  bstDepthSumOn tail (.node leftTree pivot rightTree) by
                simp [bstDepthSumOn, Chapter12.BSTree.depth]]
            rw [hsplit, hleftDepth, hrightDepth]
            omega
          calc
            quickSortComparisonsFuel (fuel + 1) (pivot :: tail) =
                tail.length + quickSortComparisonsFuel fuel left +
                  quickSortComparisonsFuel fuel right := by
              simp [quickSortComparisonsFuel, hleft, hright]
            _ = tail.length + bstDepthSumOn left leftTree +
                  bstDepthSumOn right rightTree := by
              simp only [leftTree, rightTree]
              rw [ihLeft, ihRight]
            _ = bstDepthSumOn (pivot :: tail)
                  (Chapter12.BSTree.buildFromList (pivot :: tail)) := hdepthRec.symm

/-- Chapter 7 and Chapter 12 use definitionally identical encodings of a
permutation as an insertion/input list. -/
theorem randomizedQuicksortInput_eq_permKeys {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortInput priority = Chapter12.BSTree.permKeys priority := rfl

/-- On a sampled permutation, executable quicksort comparisons equal total
BST depth over all ranks. -/
theorem quickSortComparisons_randomizedInput_eq_totalDepth {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    quickSortComparisons (randomizedQuicksortInput priority) =
      ∑ j : Fin n,
        Chapter12.BSTree.depth j.val (Chapter12.BSTree.buildFromPerm priority) := by
  have hnodup : (randomizedQuicksortInput priority).Nodup := by
    exact (randomizedQuicksortInput_perm_range priority).nodup_iff.mpr
      List.nodup_range
  have hrun := quickSortComparisonsFuel_eq_bstDepthSumOn
    (randomizedQuicksortInput priority).length
    (randomizedQuicksortInput priority) (by omega) hnodup
  rw [show quickSortComparisons (randomizedQuicksortInput priority) =
      quickSortComparisonsFuel (randomizedQuicksortInput priority).length
        (randomizedQuicksortInput priority) from rfl]
  rw [hrun]
  have hperm := randomizedQuicksortInput_perm_range priority
  have hsum := (hperm.map (fun x =>
    Chapter12.BSTree.depth x (Chapter12.BSTree.buildFromPerm priority))).sum_eq
  rw [show Chapter12.BSTree.buildFromList (randomizedQuicksortInput priority) =
      Chapter12.BSTree.buildFromPerm priority by
        rw [randomizedQuicksortInput_eq_permKeys]
        rfl]
  unfold bstDepthSumOn
  rw [hsum]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat =>
      Chapter12.BSTree.depth j (Chapter12.BSTree.buildFromPerm priority)) n]
  have hrange :
      (Finset.range n).sum (fun j : Nat =>
          Chapter12.BSTree.depth j (Chapter12.BSTree.buildFromPerm priority)) =
        ((List.range n).map (fun j : Nat =>
          Chapter12.BSTree.depth j
            (Chapter12.BSTree.buildFromPerm priority))).sum := by
    rw [← List.toFinset_range n]
    exact List.sum_toFinset
      (fun j : Nat =>
        Chapter12.BSTree.depth j (Chapter12.BSTree.buildFromPerm priority))
      (l := List.range n)
      List.nodup_range
  exact hrange.symm

end Chapter07
end CLRS
