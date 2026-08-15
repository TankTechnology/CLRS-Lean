import CLRSLean.Chapter_06.Section_06_1_Heaps
import CLRSLean.Chapter_06.Section_06_2_Maintaining_Heap_Property
import CLRSLean.Chapter_06.Section_06_3_Building_A_Heap
import CLRSLean.Chapter_06.Section_06_4_Heapsort
import CLRSLean.Chapter_06.Section_06_4_Heapsort.CostedExecution
import CLRSLean.Chapter_06.Section_06_5_Priority_Queues

/-!
# Chapter 6 legacy import compatibility

These checks keep the pre-section-layout module paths source-compatible.
-/

#check CLRS.Chapter06.parent_lt_self
#check CLRS.Chapter06.ArrayMaxHeap.getElem_le_root
#check CLRS.Chapter06.maxHeapifyFuel_root_isMaxHeap
#check CLRS.Chapter06.arrayBuildMaxHeap_correct
#check CLRS.Chapter06.arrayHeapSortInPlace_correct
#check CLRS.Chapter06.arrayHeapSort_correct
#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_cost
#check CLRS.Chapter06.heapSortNLogNBound_isBigO_nlogn
#check CLRS.Chapter06.heapInsert_orderedDesc
#check CLRS.Chapter06.arrayHeapMaximum?_max
