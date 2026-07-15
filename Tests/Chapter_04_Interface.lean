import CLRSLean.Chapter_04

namespace CLRS
namespace Chapter04

#check maxPrefixLinear
#check maxPrefixLinear_result_correct
#check maxSuffixLinear
#check maxSuffixLinear_result_correct
#check maxCrossingSubarrayLinear
#check maxCrossingSubarrayLinear_result_correct
#check maxSubarrayDivide
#check maxSubarrayDivideCosted
#check maxSubarrayDivideCosted_result
#check maxSubarrayDivideCosted_correct
#check maxSubarrayDivideCost
#check maxSubarrayDivideCosted_cost_eq
#check maxSubarrayDivideCost_unfold
#check maxSubarrayDivideCost_monotone
#check maxSubarrayDivideCost_power_sandwich
#check maxSubarrayDivideCost_pow_two
#check maxSubarrayDivideCost_isBigTheta_nlogn

example : maxPrefixLinear ([] : List Int) = none := by native_decide

example : maxPrefixLinear [1, 0] = some [1] := by native_decide

example : maxSuffixLinear [-2, 3] = some [3] := by native_decide

example : maxCrossingSubarrayLinear [-2, 3] [4, -9] = some [3, 4] := by
  native_decide

example : maxCrossingSubarrayLinear [] [1] = none := by native_decide

example : maxCrossingSubarrayLinear [1] [] = none := by native_decide

example : maxSubarrayDivide [] = none := by native_decide

example : maxSubarrayDivide [-7] = some [-7] := by native_decide

-- The tie on the left suffix is resolved by the linear crossing scan: the
-- older Cartesian enumerator would return `[0, 1, 2]` here.
example : (maxSubarrayDivideCosted [0, 1, 2, -100]).1 = some [1, 2] := by
  native_decide

example :
    IsMaxSubarrayResult [2, -5, 4, 3, -9]
      (maxSubarrayDivideCosted [2, -5, 4, 3, -9]).1 := by
  exact maxSubarrayDivideCosted_correct _

example (xs : List Int) :
    (maxSubarrayDivideCosted xs).2 = maxSubarrayDivideCost xs.length := by
  exact maxSubarrayDivideCosted_cost_eq xs

end Chapter04
end CLRS
