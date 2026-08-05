import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check binaryLowerBound
#check binaryLowerBound_index_le_length
#check binaryLowerBound_partition
#check binaryLowerBound_work_le_log
#check LowerBoundSpec
#check binaryLowerBound_span_eq_work
#check binaryLowerBound_span_le_log
#check pMerge
#check pMerge_value_sorted
#check pMerge_value_perm
#check pMerge_value_length
#check pMerge_correct
#check pMerge_childSizes_add_one
#check pMerge_childSize_le_threeQuarters
#check pMerge_work_step_eq
#check pMerge_span_step_eq
#check pMerge_work_step_le
#check pMerge_span_step_le
#check pMerge_work_lower
#check pMerge_work_upper
#check pMerge_span_upper
#check pMerge_interleaved_span_lower
#check pMergeSort
#check pMergeSort_value_sorted
#check pMergeSort_value_perm
#check pMergeSort_value_length
#check pMergeSort_correct

/-! Executable P-MERGE-SORT covers both base branches, a reversed odd-length
input, and duplicate-heavy data. -/

example : (pMergeSort ([] : List ℕ)).value = [] := by native_decide
example : (pMergeSort ([] : List ℕ)).work = 0 := by native_decide
example : (pMergeSort ([] : List ℕ)).span = 0 := by native_decide

example : (pMergeSort [7]).value = [7] := by native_decide
example : (pMergeSort [7]).work = 1 := by native_decide
example : (pMergeSort [7]).span = 1 := by native_decide

example : (pMergeSort [5, 1, 4, 2, 3]).value = [1, 2, 3, 4, 5] := by
  native_decide

example : (pMergeSort [3, 1, 2, 1, 3, 2, 1]).value = [1, 1, 1, 2, 2, 3, 3] := by
  native_decide

/-! The reader-facing theorem, rather than direct evaluation alone, exposes
sortedness, multiset preservation, and exact output length. -/

example : PMergeSortSpec [5, 1, 4, 2, 3]
    (pMergeSort [5, 1, 4, 2, 3]).value := by
  exact pMergeSort_correct [5, 1, 4, 2, 3]

example : (pMergeSort [5, 1, 4, 2, 3]).value.Pairwise (· ≤ ·) := by
  exact pMergeSort_value_sorted [5, 1, 4, 2, 3]

example : (pMergeSort [3, 1, 2, 1]).value.Perm [3, 1, 2, 1] := by
  exact pMergeSort_value_perm [3, 1, 2, 1]

example : (pMergeSort [5, 1, 4, 2, 3]).value.length = 5 := by
  simpa using pMergeSort_value_length [5, 1, 4, 2, 3]

/-! The executable P-MERGE boundary covers empty inputs, an empty secondary
input, interleaving inputs, duplicates, and normalization by swapping the
longer input into the primary position. -/

example : (pMerge ([] : List ℕ) []).value = [] := by native_decide

example : (pMerge [7] []).value = [7] := by native_decide
example : (pMerge [7] []).work = 2 := by native_decide
example : (pMerge [7] []).span = 2 := by native_decide

/-! Structural accounting includes small totals and odd, unequal normalized
splits.  The step equations expose the exact two units beyond binary search:
one fork/join and one pivot placement. -/

example :
    let S := mergeSplit [7] ([] : List ℕ) (by simp)
    S.leftSize + S.rightSize + 1 = S.totalSize := by
  exact pMerge_childSizes_add_one _

example :
    let S := mergeSplit [7] ([] : List ℕ) (by simp)
    S.leftSize ≤ S.totalSize - S.totalSize / 4 ∧
      S.rightSize ≤ S.totalSize - S.totalSize / 4 := by
  exact pMerge_childSize_le_threeQuarters _

example :
    let S := mergeSplit [2, 4] [1, 3, 5] (by simp)
    S.leftSize ≤ S.totalSize - S.totalSize / 4 ∧
      S.rightSize ≤ S.totalSize - S.totalSize / 4 := by
  exact pMerge_childSize_le_threeQuarters _

example :
    let S := mergeSplit [2, 4] [1, 3, 5] (by simp)
    (pMerge [2, 4] [1, 3, 5]).work =
      S.search.work +
        (pMerge S.lowerPrimary S.lowerSecondary).work +
        (pMerge S.upperPrimary S.upperSecondary).work + 2 := by
  exact pMerge_work_step_eq _ _ (by simp)

example :
    let S := mergeSplit [2, 4] [1, 3, 5] (by simp)
    (pMerge [2, 4] [1, 3, 5]).span =
      S.search.span +
        max (pMerge S.lowerPrimary S.lowerSecondary).span
          (pMerge S.upperPrimary S.upperSecondary).span + 2 := by
  exact pMerge_span_step_eq _ _ (by simp)

example : (pMerge [1, 3, 5] [2, 4, 6]).value = [1, 2, 3, 4, 5, 6] := by
  native_decide

example : (pMerge [1, 2, 2] [2, 2, 3]).value = [1, 2, 2, 2, 2, 3] := by
  native_decide

-- The second input is longer and has odd total length, so it becomes primary.
example : (pMerge [2, 4] [1, 3, 5]).value = [1, 2, 3, 4, 5] := by
  native_decide

/-! The theorem interface covers duplicates and the odd-total normalization
branch, independently of the direct-execution examples above. -/

example : (pMerge [1, 2, 2] [2, 2, 3]).value.Pairwise (· ≤ ·) := by
  exact pMerge_value_sorted [1, 2, 2] [2, 2, 3] (by simp) (by simp)

example : (pMerge [1, 2, 2] [2, 2, 3]).value.Perm
    ([1, 2, 2] ++ [2, 2, 3]) := by
  exact pMerge_value_perm [1, 2, 2] [2, 2, 3] (by simp) (by simp)

example : (pMerge [1, 2, 2] [2, 2, 3]).value.length = 6 := by
  simpa using pMerge_value_length [1, 2, 2] [2, 2, 3] (by simp) (by simp)

example : PMergeSpec [2, 4] [1, 3, 5] (pMerge [2, 4] [1, 3, 5]).value := by
  exact pMerge_correct [2, 4] [1, 3, 5] (by simp) (by simp)

example : (pMerge [2, 4] [1, 3, 5]).value.Pairwise (· ≤ ·) := by
  exact (pMerge_correct [2, 4] [1, 3, 5] (by simp) (by simp)).sorted

example : (pMerge [2, 4] [1, 3, 5]).value.Perm ([2, 4] ++ [1, 3, 5]) := by
  exact (pMerge_correct [2, 4] [1, 3, 5] (by simp) (by simp)).perm

example : (pMerge [2, 4] [1, 3, 5]).value.length = 5 := by
  simpa using (pMerge_correct [2, 4] [1, 3, 5] (by simp) (by simp)).length_eq

/-! The pointwise work theorems cover the zero boundary, a singleton, a
duplicate-heavy merge, and the odd unequal normalization branch. -/

example :
    0 ≤ (pMerge ([] : List ℕ) []).work + 1 ∧
      (pMerge ([] : List ℕ) []).work ≤ 64 * (0 + 0 + 1) := by
  exact ⟨pMerge_work_lower [] [], pMerge_work_upper [] []⟩

example :
    1 ≤ (pMerge [7] ([] : List ℕ)).work + 1 ∧
      (pMerge [7] ([] : List ℕ)).work ≤ 64 * (1 + 0 + 1) := by
  exact ⟨pMerge_work_lower [7] [], pMerge_work_upper [7] []⟩

example :
    3 + 3 ≤ (pMerge [1, 2, 2] [2, 2, 3]).work + 1 ∧
      (pMerge [1, 2, 2] [2, 2, 3]).work ≤ 64 * (3 + 3 + 1) := by
  exact ⟨pMerge_work_lower [1, 2, 2] [2, 2, 3],
    pMerge_work_upper [1, 2, 2] [2, 2, 3]⟩

example :
    2 + 3 ≤ (pMerge [2, 4] [1, 3, 5]).work + 1 ∧
      (pMerge [2, 4] [1, 3, 5]).work ≤ 64 * (2 + 3 + 1) := by
  exact ⟨pMerge_work_lower [2, 4] [1, 3, 5],
    pMerge_work_upper [2, 4] [1, 3, 5]⟩

-- This direct execution check independently confirms the concrete upper bound.
example : (pMerge [1, 2, 2] [2, 2, 3]).work ≤ 64 * 7 := by native_decide

/-! The pointwise span theorem covers the empty and singleton boundaries,
duplicates, and the odd unequal normalization branch. -/

example : (pMerge ([] : List ℕ) []).span ≤
    64 * (Nat.log 2 (0 + 0) + 1) ^ 2 := pMerge_span_upper [] []

example : (pMerge [7] ([] : List ℕ)).span ≤
    64 * (Nat.log 2 (1 + 0) + 1) ^ 2 := pMerge_span_upper [7] []

example : (pMerge [1, 2, 2] [2, 2, 3]).span ≤
    64 * (Nat.log 2 (3 + 3) + 1) ^ 2 :=
  pMerge_span_upper [1, 2, 2] [2, 2, 3]

example : (pMerge [2, 4] [1, 3, 5]).span ≤
    64 * (Nat.log 2 (2 + 3) + 1) ^ 2 :=
  pMerge_span_upper [2, 4] [1, 3, 5]

/-! The interleaved witnesses are genuinely sorted inputs.  Small concrete
executions complement the uniform theorem. -/

example (k : ℕ) : PMergeSpec (evenKeys (2 ^ k)) (oddKeys (2 ^ k))
    (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).value := by
  exact pMerge_correct _ _ (evenKeys_sorted _) (oddKeys_sorted _)

example : (0 + 1) ^ 2 ≤
    8 * (pMerge (evenKeys (2 ^ 0)) (oddKeys (2 ^ 0))).span := by native_decide

example : (1 + 1) ^ 2 ≤
    8 * (pMerge (evenKeys (2 ^ 1)) (oddKeys (2 ^ 1))).span := by native_decide

example : (2 + 1) ^ 2 ≤
    8 * (pMerge (evenKeys (2 ^ 2)) (oddKeys (2 ^ 2))).span := by native_decide

example : (3 + 1) ^ 2 ≤
    8 * (pMerge (evenKeys (2 ^ 3)) (oddKeys (2 ^ 3))).span := by native_decide

example (k : ℕ) : (k + 1) ^ 2 ≤
    8 * (pMerge (evenKeys (2 ^ k)) (oddKeys (2 ^ k))).span :=
  pMerge_interleaved_span_lower k

example : (binaryLowerBound ([] : List ℕ) 3).value = 0 := by native_decide
example : (binaryLowerBound ([] : List ℕ) 3).work = 0 := by native_decide
example : (binaryLowerBound ([] : List ℕ) 3).span = 0 := by native_decide
example :
    (binaryLowerBound ([] : List ℕ) 3).work =
      (binaryLowerBound ([] : List ℕ) 3).span := by
  native_decide

example : (binaryLowerBound [1, 1, 1] 1).value = 0 := by native_decide
example : (binaryLowerBound [1, 1, 1] 1).work = 2 := by native_decide
example : (binaryLowerBound [1, 1, 1] 1).span = 2 := by native_decide
example :
    (binaryLowerBound [1, 1, 1] 1).work = (binaryLowerBound [1, 1, 1] 1).span := by
  native_decide

example : (binaryLowerBound [1, 3, 5] 0).value = 0 := by native_decide
example :
    (binaryLowerBound [1, 3, 5] 0).work = (binaryLowerBound [1, 3, 5] 0).span := by
  native_decide
example : (binaryLowerBound [1, 3, 5] 4).value = 2 := by native_decide
example : (binaryLowerBound [1, 3, 5] 4).work = 2 := by native_decide
example : (binaryLowerBound [1, 3, 5] 4).span = 2 := by native_decide
example :
    (binaryLowerBound [1, 3, 5] 4).work = (binaryLowerBound [1, 3, 5] 4).span := by
  native_decide

example : (binaryLowerBound [1, 2, 2, 2, 3] 2).value = 1 := by native_decide
example : (binaryLowerBound [1, 2, 2, 2, 3] 2).work = 3 := by native_decide
example : (binaryLowerBound [1, 2, 2, 2, 3] 2).span = 3 := by native_decide
example :
    (binaryLowerBound [1, 2, 2, 2, 3] 2).work =
      (binaryLowerBound [1, 2, 2, 2, 3] 2).span := by
  native_decide

example : (binaryLowerBound [1, 3, 5] 6).value = 3 := by native_decide
example : (binaryLowerBound [1, 3, 5] 6).work = 2 := by native_decide
example : (binaryLowerBound [1, 3, 5] 6).span = 2 := by native_decide
example :
    (binaryLowerBound [1, 3, 5] 6).work = (binaryLowerBound [1, 3, 5] 6).span := by
  native_decide

/-! The theorem interface, rather than computation alone, exposes all three
fields of the duplicate-sensitive partition specification. -/

example : LowerBoundSpec [1, 2, 2, 2, 3] 2
    (binaryLowerBound [1, 2, 2, 2, 3] 2).value := by
  exact binaryLowerBound_partition [1, 2, 2, 2, 3] 2 (by simp)

example : (binaryLowerBound [1, 2, 2, 2, 3] 2).value ≤ 5 := by
  exact (binaryLowerBound_partition [1, 2, 2, 2, 3] 2 (by simp)).index_le_length

example : ∀ x ∈ [1, 2, 2, 2, 3].take
    (binaryLowerBound [1, 2, 2, 2, 3] 2).value, x < 2 := by
  exact (binaryLowerBound_partition [1, 2, 2, 2, 3] 2 (by simp)).left_lt

example : ∀ x ∈ [1, 2, 2, 2, 3].drop
    (binaryLowerBound [1, 2, 2, 2, 3] 2).value, 2 ≤ x := by
  exact (binaryLowerBound_partition [1, 2, 2, 2, 3] 2 (by simp)).right_ge

-- The index bound deliberately has no sortedness premise.
example : (binaryLowerBound [3, 1, 2] 2).value ≤ 3 := by
  exact binaryLowerBound_index_le_length [3, 1, 2] 2

example : (binaryLowerBound [1, 2, 2, 2, 3] 2).work ≤ Nat.log 2 5 + 1 := by
  exact binaryLowerBound_work_le_log [1, 2, 2, 2, 3] 2

example : (binaryLowerBound [1, 2, 2, 2, 3] 2).span =
    (binaryLowerBound [1, 2, 2, 2, 3] 2).work := by
  exact binaryLowerBound_span_eq_work [1, 2, 2, 2, 3] 2

example : (binaryLowerBound [1, 2, 2, 2, 3] 2).span ≤ Nat.log 2 5 + 1 := by
  exact binaryLowerBound_span_le_log [1, 2, 2, 2, 3] 2

#print axioms binaryLowerBound_partition
#print axioms binaryLowerBound_work_le_log
#print axioms binaryLowerBound_span_le_log
#print axioms pMerge_correct
#print axioms pMerge_value_sorted
#print axioms pMerge_value_perm
#print axioms pMerge_value_length
#print axioms pMerge_childSizes_add_one
#print axioms pMerge_childSize_le_threeQuarters
#print axioms pMerge_work_lower
#print axioms pMerge_work_upper
#print axioms pMerge_span_upper
#print axioms pMerge_interleaved_span_lower
#print axioms pMergeSort_correct
#print axioms pMergeSort_value_sorted
#print axioms pMergeSort_value_perm
#print axioms pMergeSort_value_length

end CLRS.Chapter27
