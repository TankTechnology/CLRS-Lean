import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.OperationalBridge.ExecutionToBST
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.OperationalBridge.UnorderedPairs

/-!
# From the CLRS comparison trace to binary-search-tree depth

The pair characterization of randomized quicksort and the ancestor
characterization of a randomly built BST both say that one endpoint is the
first key in the same closed rank interval.  This module makes that shared
semantics explicit and converts the pair count into total BST depth.
-/

namespace CLRS
namespace Chapter07

open CLRS.Probability

private noncomputable instance ancestorDecidable
    (x y : Nat) (tree : Chapter12.BSTree) :
    Decidable (Chapter12.BSTree.isAncestorOf x y tree) :=
  Classical.propDecidable _

/-- The embedded natural-number interval used by Chapter 7 is the ordinary
closed interval of bounded ranks used by Chapter 12. -/
theorem rangeFin_eq_intervalIcc {n : Nat} (i j : Fin n) (hij : i.val < j.val) :
    rangeFin n i.val j.val (Nat.le_of_lt hij) j.isLt = Finset.Icc i j := by
  ext k
  simp [rangeFin, Finset.mem_Icc, Fin.ext_iff]

private theorem isFirstIn_Icc_left_iff_firstInInterval {n : Nat}
    (i j : Fin n) (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    IsFirstIn (Finset.Icc i j) i priority ↔
      Chapter12.BSTree.firstInInterval priority i j := by
  have hle : i ≤ j := by exact Fin.mk_le_mk.mpr (Nat.le_of_lt hij)
  simp [IsFirstIn, pos, Chapter12.BSTree.firstInInterval,
    Finset.mem_Icc, hle]

private theorem isFirstIn_Icc_right_iff_firstInInterval {n : Nat}
    (i j : Fin n) (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    IsFirstIn (Finset.Icc i j) j priority ↔
      Chapter12.BSTree.firstInInterval priority j i := by
  have hle : i ≤ j := by exact Fin.mk_le_mk.mpr (Nat.le_of_lt hij)
  simp [IsFirstIn, pos, Chapter12.BSTree.firstInInterval,
    Finset.mem_Icc, hle]

/-- A rank pair is compared by quicksort exactly when one endpoint is an
ancestor of the other in the BST built from the same priority permutation. -/
theorem comparedInQuicksort_iff_ancestor {n : Nat} (i j : Fin n)
    (hij : i.val < j.val) (priority : Equiv.Perm (Fin n)) :
    comparedInQuicksort n i.val j.val hij j.isLt priority ↔
      Chapter12.BSTree.isAncestorOf i.val j.val
          (Chapter12.BSTree.buildFromPerm priority) ∨
        Chapter12.BSTree.isAncestorOf j.val i.val
          (Chapter12.BSTree.buildFromPerm priority) := by
  unfold comparedInQuicksort
  dsimp only
  rw [rangeFin_eq_intervalIcc i j hij]
  have hi : (⟨i.val, Nat.lt_trans hij j.isLt⟩ : Fin n) = i := Fin.ext rfl
  have hj : (⟨j.val, j.isLt⟩ : Fin n) = j := Fin.ext rfl
  rw [hi, hj]
  rw [isFirstIn_Icc_left_iff_firstInInterval i j hij priority]
  rw [isFirstIn_Icc_right_iff_firstInInterval i j hij priority]
  rw [← Chapter12.BSTree.isAncestorOf_buildFromPerm_iff_firstInInterval]
  rw [← Chapter12.BSTree.isAncestorOf_buildFromPerm_iff_firstInInterval]

private noncomputable def ancestorBit {n : Nat} (priority : Equiv.Perm (Fin n))
    (i j : Fin n) : Nat :=
  if Chapter12.BSTree.isAncestorOf i.val j.val
      (Chapter12.BSTree.buildFromPerm priority) then 1 else 0

private theorem not_ancestor_both {n : Nat} (priority : Equiv.Perm (Fin n))
    {i j : Fin n} (hne : i ≠ j) :
    ¬(Chapter12.BSTree.isAncestorOf i.val j.val
          (Chapter12.BSTree.buildFromPerm priority) ∧
        Chapter12.BSTree.isAncestorOf j.val i.val
          (Chapter12.BSTree.buildFromPerm priority)) := by
  intro hboth
  have hfirstI :=
    (Chapter12.BSTree.isAncestorOf_buildFromPerm_iff_firstInInterval
      priority i j).mp hboth.1
  have hfirstJ :=
    (Chapter12.BSTree.isAncestorOf_buildFromPerm_iff_firstInInterval
      priority j i).mp hboth.2
  have hposIJ : (priority.symm i : Nat) ≤ (priority.symm j : Nat) :=
    hfirstI j (min_le_right _ _) (le_max_right _ _)
  have hposJI : (priority.symm j : Nat) ≤ (priority.symm i : Nat) :=
    hfirstJ i (min_le_right _ _) (le_max_right _ _)
  have hpos : priority.symm i = priority.symm j :=
    Fin.ext (Nat.le_antisymm hposIJ hposJI)
  exact hne (priority.symm.injective hpos)

private theorem randomizedQuicksortComparisonBit_eq_ancestorBits {n : Nat}
    (i j : Fin n) (hij : i.val < j.val)
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortComparisonBit i j hij priority =
      ancestorBit priority i j + ancestorBit priority j i := by
  have hne : i ≠ j := by
    intro h
    exact (Nat.ne_of_lt hij) (congrArg Fin.val h)
  have hiff := comparedInQuicksort_iff_ancestor i j hij priority
  unfold randomizedQuicksortComparisonBit ancestorBit
  simp only [hiff]
  by_cases hleft : Chapter12.BSTree.isAncestorOf i.val j.val
      (Chapter12.BSTree.buildFromPerm priority)
  · have hright : ¬Chapter12.BSTree.isAncestorOf j.val i.val
        (Chapter12.BSTree.buildFromPerm priority) := by
      intro hright
      exact not_ancestor_both priority hne ⟨hleft, hright⟩
    simp [hleft, hright]
  · by_cases hright : Chapter12.BSTree.isAncestorOf j.val i.val
        (Chapter12.BSTree.buildFromPerm priority)
    · simp [hleft, hright]
    · simp [hleft, hright]

/-- The depth of one key is the number of its strict ancestors. -/
theorem depth_eq_sum_strictAncestorBits {n : Nat}
    (priority : Equiv.Perm (Fin n)) (j : Fin n) :
    Chapter12.BSTree.depth j.val
        (Chapter12.BSTree.buildFromPerm priority) =
      ∑ i : Fin n,
        if i ≠ j ∧ Chapter12.BSTree.isAncestorOf i.val j.val
            (Chapter12.BSTree.buildFromPerm priority) then 1 else 0 := by
  classical
  let tree := Chapter12.BSTree.buildFromPerm priority
  let allAncestors : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n =>
      Chapter12.BSTree.isAncestorOf i.val j.val tree)
  let strictAncestors : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n =>
      i ≠ j ∧ Chapter12.BSTree.isAncestorOf i.val j.val tree)
  have hself : Chapter12.BSTree.isAncestorOf j.val j.val tree := by
    simpa [tree] using
      Chapter12.BSTree.isAncestorOf_self_buildFromPerm priority j
  have hselfMem : j ∈ allAncestors := by
    simp [allAncestors, hself]
  have herase : allAncestors.erase j = strictAncestors := by
    ext i
    simp [allAncestors, strictAncestors]
  have hcard : strictAncestors.card + 1 = allAncestors.card := by
    simpa [herase] using Finset.card_erase_add_one hselfMem
  have hordered : Chapter12.BSTree.Ordered tree := by
    simpa [tree, Chapter12.BSTree.buildFromPerm] using
      Chapter12.BSTree.buildFromList_ordered
      (Chapter12.BSTree.permKeys priority)
  have hbounded : ∀ z, Chapter12.BSTree.InTree z tree → z < n := by
    intro z hz
    exact Chapter12.BSTree.InTree_buildFromPerm_lt priority (by simpa [tree] using hz)
  have hcount : Chapter12.BSTree.ancestorCount j.val tree = allAncestors.card := by
    change Chapter12.BSTree.ancestorCount j.val tree =
      (Finset.univ.filter (fun i : Fin n =>
        Chapter12.BSTree.isAncestorOf i.val j.val tree)).card
    exact Chapter12.BSTree.ancestorCount_eq_sum j.val tree hordered hbounded
  have hdepth : Chapter12.BSTree.ancestorCount j.val tree =
      Chapter12.BSTree.depth j.val tree + 1 :=
    Chapter12.BSTree.ancestorCount_eq_depth_add_one j.val tree hself
  have hsum :
      (∑ i : Fin n,
        if i ≠ j ∧ Chapter12.BSTree.isAncestorOf i.val j.val tree
          then 1 else 0) = strictAncestors.card := by
    simp [strictAncestors]
  change Chapter12.BSTree.depth j.val tree = _
  rw [hsum]
  omega

/-- The executable CLRS pair-trace counter is total BST depth for the tree
built from the same permutation. -/
theorem randomizedQuicksortComparisonCount_eq_totalDepth {n : Nat}
    (priority : Equiv.Perm (Fin n)) :
    randomizedQuicksortComparisonCount priority =
      ∑ j : Fin n,
        Chapter12.BSTree.depth j.val
          (Chapter12.BSTree.buildFromPerm priority) := by
  classical
  calc
    randomizedQuicksortComparisonCount priority =
        ∑ i : Fin n, ∑ j : Fin n,
          if hij : i.val < j.val then
            ancestorBit priority i j + ancestorBit priority j i else 0 := by
      unfold randomizedQuicksortComparisonCount
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split
      · exact randomizedQuicksortComparisonBit_eq_ancestorBits i j _ priority
      · rfl
    _ = ∑ i : Fin n, ∑ j : Fin n,
          if i ≠ j then ancestorBit priority i j else 0 := by
      exact (sum_offDiagonal_eq_sum_strictPairs (ancestorBit priority)).symm
    _ = ∑ j : Fin n, ∑ i : Fin n,
          if i ≠ j then ancestorBit priority i j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n,
          Chapter12.BSTree.depth j.val
            (Chapter12.BSTree.buildFromPerm priority) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [depth_eq_sum_strictAncestorBits priority j]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ancestorBit]
      by_cases hne : i ≠ j <;>
        by_cases hancestor : Chapter12.BSTree.isAncestorOf i.val j.val
          (Chapter12.BSTree.buildFromPerm priority) <;>
        simp [hne, hancestor]

end Chapter07
end CLRS
