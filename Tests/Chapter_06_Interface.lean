import CLRSLean.Chapter_06

#check CLRS.Chapter06.maxHeapifyFuelWithCost
#check CLRS.Chapter06.maxHeapifyFuelWithCost_result
#check CLRS.Chapter06.maxHeapifyFuelWithCost_cost_le_fuel
#check CLRS.Chapter06.buildMaxHeapLoopWithCost
#check CLRS.Chapter06.buildMaxHeapLoopWithCost_result
#check CLRS.Chapter06.arrayBuildMaxHeapWithCost
#check CLRS.Chapter06.arrayBuildMaxHeapWithCost_result
#check CLRS.Chapter06.arrayBuildMaxHeapWithCost_correct
#check CLRS.Chapter06.arrayHeapSortStepWithCost
#check CLRS.Chapter06.arrayHeapSortStepWithCost_result
#check CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost
#check CLRS.Chapter06.arrayHeapSortInPlaceLoopWithCost_result
#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost
#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost_result
#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_cost
#check CLRS.Chapter06.maxHeapifyControlBound_isBigO_n
#check CLRS.Chapter06.buildMaxHeapControlBound_isBigO_nsq
#check CLRS.Chapter06.heapSortControlBound_isBigO_nsq

example (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (CLRS.Chapter06.maxHeapifyFuelWithCost fuel a heapSize i).1 =
      CLRS.Chapter06.maxHeapifyFuel fuel a heapSize i :=
  CLRS.Chapter06.maxHeapifyFuelWithCost_result fuel a heapSize i

example (xs : List Nat) :
    (CLRS.Chapter06.arrayHeapSortInPlaceWithCost xs).1 =
      CLRS.Chapter06.arrayHeapSortInPlace xs :=
  CLRS.Chapter06.arrayHeapSortInPlaceWithCost_result xs
