import CLRSLean.FourthEdition.Chapter_07

/-! # Fourth-edition Chapter 7 explicit-randomness interface -/

namespace CLRS
namespace Chapter07

#check priorityPivot_uniform
#check randomizedQuicksortInput
#check randomizedQuicksortInput_perm_range
#check randomizedQuicksortOutput
#check randomizedQuicksortOutput_eq_quickSort
#check randomizedQuicksortOutput_correct
#check randomizedQuicksortComparisonCount
#check comparedIndicator_expectation
#check explicitRandomizedQuicksortExpectedComparisons
#check explicitRandomizedQuicksortExpectedComparisons_eq_pairSum
#check explicitRandomizedQuicksortExpectedComparisons_eq
#check explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn

example : randomizedQuicksortComparisonCount (Equiv.refl (Fin 4)) = 6 := by
  native_decide

example : randomizedQuicksortComparisonCount (Equiv.swap (0 : Fin 3) 1) = 2 := by
  native_decide

end Chapter07
end CLRS
