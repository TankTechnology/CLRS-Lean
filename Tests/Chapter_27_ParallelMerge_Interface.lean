import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check binaryLowerBound
#check binaryLowerBound_index_le_length
#check binaryLowerBound_partition
#check binaryLowerBound_work_le_log
#check LowerBoundSpec
#check binaryLowerBound_span_eq_work
#check binaryLowerBound_span_le_log

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

end CLRS.Chapter27
