import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check binaryLowerBound
#check binaryLowerBound_index_le_length
#check binaryLowerBound_partition
#check binaryLowerBound_work_le_log

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

end CLRS.Chapter27
