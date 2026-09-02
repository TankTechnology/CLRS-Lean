import CLRSLean.Chapter_08.Section_08_1_Lower_Bound_For_Sorting
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.CountTables
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort.MutableOutputArray
import CLRSLean.Chapter_08.Section_08_3_Radix_Sort
import CLRSLean.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Chapter 8 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter08.comparisonSort_worstCase_lowerBound
#check CLRS.Chapter08.countingSortBy_correct
#check CLRS.Chapter08.MutableOutput.countingSortArray_correct
#check CLRS.Chapter08.radixSortBy_correct_stable
#check CLRS.Chapter08.radixSortNatByCost_bigO
#check CLRS.Chapter08.bucketSortBy_correct
#check CLRS.Chapter08.expectedBucketSortByRankCost_isBigO
