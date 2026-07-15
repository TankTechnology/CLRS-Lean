import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_06.Section_06_4_Heapsort

/-!
# Costed execution for CLRS heapsort

This module instruments the executable Chapter 6 heap operations with an
abstract unit control-step count.  Projecting the first component recovers the
existing execution exactly.  The metric deliberately counts recursive frames
and loop steps; it is not a RAM-cost model for Lean lists.
-/

namespace CLRS
namespace Chapter06

open Chapter03

/-! ## Costed `MAX-HEAPIFY` -/

/-- `MAX-HEAPIFY` paired with the number of visited recursive frames. -/
def maxHeapifyFuelWithCost : Nat → List Nat → Nat → Nat → List Nat × Nat
  | 0, a, _, _ => (a, 0)
  | fuel + 1, a, heapSize, i =>
      let largest := maxChildIndex a heapSize i
      if largest = i then
        (a, 1)
      else
        let next := maxHeapifyFuelWithCost fuel
          (swapAt a i largest) heapSize largest
        (next.1, next.2 + 1)

/-- Erasing the control-step count recovers the existing fuelled heapify. -/
theorem maxHeapifyFuelWithCost_result
    (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (maxHeapifyFuelWithCost fuel a heapSize i).1 =
      maxHeapifyFuel fuel a heapSize i := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuelWithCost, maxHeapifyFuel]
  | succ fuel ih =>
      simp only [maxHeapifyFuelWithCost, maxHeapifyFuel]
      split
      · rfl
      · exact ih _ _

/-- A heapify run visits at most one recursive frame per unit of fuel. -/
theorem maxHeapifyFuelWithCost_cost_le_fuel
    (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (maxHeapifyFuelWithCost fuel a heapSize i).2 ≤ fuel := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuelWithCost]
  | succ fuel ih =>
      simp only [maxHeapifyFuelWithCost]
      split
      · simp
      · have hrec := ih (swapAt a i (maxChildIndex a heapSize i))
          (maxChildIndex a heapSize i)
        omega

end Chapter06
end CLRS
