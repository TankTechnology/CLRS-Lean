import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_06.Section_06_4_Heapsort

/-!
# Costed execution for CLRS heapsort

This module instruments the executable Chapter 6 heap operations with an
abstract unit control-step count.  Projecting the first component recovers the
existing execution exactly.  The metric counts visited `MAX-HEAPIFY` frames
and one extraction/swap transition for each nontrivial heapsort step.  Build-
loop orchestration and function calls are not charged separately, and this is
not a RAM-cost model for Lean lists.
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

/-! ## Costed bottom-up heap construction -/

/-- Bottom-up heap construction paired with the sum of heapify frame counts. -/
def buildMaxHeapLoopWithCost : Nat → List Nat → Nat → List Nat × Nat
  | 0, a, _ => (a, 0)
  | count + 1, a, heapSize =>
      let repaired := maxHeapifyFuelWithCost heapSize a heapSize count
      let rest := buildMaxHeapLoopWithCost count repaired.1 heapSize
      (rest.1, repaired.2 + rest.2)

/-- Erasing build-loop cost recovers the existing bottom-up builder. -/
theorem buildMaxHeapLoopWithCost_result
    (count : Nat) (a : List Nat) (heapSize : Nat) :
    (buildMaxHeapLoopWithCost count a heapSize).1 =
      buildMaxHeapLoop count a heapSize := by
  induction count generalizing a with
  | zero =>
      simp [buildMaxHeapLoopWithCost, buildMaxHeapLoop]
  | succ count ih =>
      simp only [buildMaxHeapLoopWithCost, buildMaxHeapLoop]
      rw [ih, maxHeapifyFuelWithCost_result]

/-- The bottom-up build loop uses at most `count * heapSize` control steps. -/
theorem buildMaxHeapLoopWithCost_cost_le
    (count : Nat) (a : List Nat) (heapSize : Nat) :
    (buildMaxHeapLoopWithCost count a heapSize).2 ≤ count * heapSize := by
  induction count generalizing a with
  | zero =>
      simp [buildMaxHeapLoopWithCost]
  | succ count ih =>
      simp only [buildMaxHeapLoopWithCost]
      have hrepair := maxHeapifyFuelWithCost_cost_le_fuel
        heapSize a heapSize count
      have hrest := ih
        (maxHeapifyFuelWithCost heapSize a heapSize count).1
      simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hrepair hrest

/-- Top-level bottom-up heap construction with its unit control-step cost. -/
def arrayBuildMaxHeapWithCost (xs : List Nat) : List Nat × Nat :=
  buildMaxHeapLoopWithCost (xs.length / 2) xs xs.length

/-- Erasing cost from the costed builder recovers `arrayBuildMaxHeap`. -/
theorem arrayBuildMaxHeapWithCost_result (xs : List Nat) :
    (arrayBuildMaxHeapWithCost xs).1 = arrayBuildMaxHeap xs := by
  simpa [arrayBuildMaxHeapWithCost, arrayBuildMaxHeap] using
    buildMaxHeapLoopWithCost_result (xs.length / 2) xs xs.length

/-- The costed builder returns a full max-heap and preserves the input multiset. -/
theorem arrayBuildMaxHeapWithCost_correct (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeapWithCost xs).1 xs.length ∧
      (arrayBuildMaxHeapWithCost xs).1.Perm xs := by
  rw [arrayBuildMaxHeapWithCost_result]
  constructor
  · simpa [arrayBuildMaxHeap, buildMaxHeapLoop_length] using
      arrayBuildMaxHeap_isMaxHeap xs
  · exact arrayBuildMaxHeap_perm xs

/-! ## Costed heapsort extraction and shrinking loop -/

/-- One heapsort extraction step paired with its heapify and swap-transition cost. -/
def arrayHeapSortStepWithCost (a : List Nat) (heapSize : Nat) : List Nat × Nat :=
  match heapSize with
  | 0 => (a, 0)
  | 1 => (a, 0)
  | newHeapSize + 2 =>
      let repaired := maxHeapifyFuelWithCost (newHeapSize + 1)
        (swapAt a 0 (newHeapSize + 1)) (newHeapSize + 1) 0
      (repaired.1, repaired.2 + 1)

/-- Erasing one costed extraction step recovers `arrayHeapSortStep`. -/
theorem arrayHeapSortStepWithCost_result (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortStepWithCost a heapSize).1 = arrayHeapSortStep a heapSize := by
  cases heapSize with
  | zero =>
      rfl
  | succ heapSize =>
      cases heapSize with
      | zero =>
          rfl
      | succ newHeapSize =>
          simpa [arrayHeapSortStepWithCost, arrayHeapSortStep] using
            maxHeapifyFuelWithCost_result (newHeapSize + 1)
              (swapAt a 0 (newHeapSize + 1)) (newHeapSize + 1) 0

/-- A single extraction step costs at most the current heap-prefix size. -/
theorem arrayHeapSortStepWithCost_cost_le_heapSize
    (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortStepWithCost a heapSize).2 ≤ heapSize := by
  cases heapSize with
  | zero =>
      rfl
  | succ heapSize =>
      cases heapSize with
      | zero =>
          rfl
      | succ newHeapSize =>
          have hheapify := maxHeapifyFuelWithCost_cost_le_fuel
            (newHeapSize + 1) (swapAt a 0 (newHeapSize + 1))
              (newHeapSize + 1) 0
          simpa [arrayHeapSortStepWithCost] using Nat.add_le_add_right hheapify 1

/-- The shrinking heapsort loop paired with accumulated extraction-step cost. -/
def arrayHeapSortInPlaceLoopWithCost :
    Nat → List Nat → Nat → List Nat × Nat
  | 0, a, _ => (a, 0)
  | fuel + 1, a, heapSize =>
      match heapSize with
      | 0 => (a, 0)
      | 1 => (a, 0)
      | newHeapSize + 2 =>
          let step := arrayHeapSortStepWithCost a (newHeapSize + 2)
          let rest := arrayHeapSortInPlaceLoopWithCost
            fuel step.1 (newHeapSize + 1)
          (rest.1, step.2 + rest.2)

/-- Erasing loop cost recovers the existing fuelled shrinking loop. -/
theorem arrayHeapSortInPlaceLoopWithCost_result
    (fuel : Nat) (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortInPlaceLoopWithCost fuel a heapSize).1 =
      arrayHeapSortInPlaceLoop fuel a heapSize := by
  induction fuel generalizing a heapSize with
  | zero =>
      rfl
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          rfl
      | succ heapSize =>
          cases heapSize with
          | zero =>
              rfl
          | succ newHeapSize =>
              simp only [arrayHeapSortInPlaceLoopWithCost,
                arrayHeapSortInPlaceLoop]
              rw [ih, arrayHeapSortStepWithCost_result]

/-- A fuelled shrinking run has a coarse rectangular control-step envelope. -/
theorem arrayHeapSortInPlaceLoopWithCost_cost_le
    (fuel : Nat) (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortInPlaceLoopWithCost fuel a heapSize).2 ≤
      fuel * (heapSize + 1) := by
  induction fuel generalizing a heapSize with
  | zero =>
      simp [arrayHeapSortInPlaceLoopWithCost]
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortInPlaceLoopWithCost]
      | succ heapSize =>
          cases heapSize with
          | zero =>
              simp [arrayHeapSortInPlaceLoopWithCost]
          | succ newHeapSize =>
              simp only [arrayHeapSortInPlaceLoopWithCost]
              have hstep := arrayHeapSortStepWithCost_cost_le_heapSize
                a (newHeapSize + 2)
              have hrest := ih
                (arrayHeapSortStepWithCost a (newHeapSize + 2)).1
                (newHeapSize + 1)
              have hsum := Nat.add_le_add hstep hrest
              calc
                (arrayHeapSortStepWithCost a (newHeapSize + 2)).2 +
                    (arrayHeapSortInPlaceLoopWithCost fuel
                      (arrayHeapSortStepWithCost a (newHeapSize + 2)).1
                      (newHeapSize + 1)).2 ≤
                    (newHeapSize + 2) + fuel * (newHeapSize + 2) := hsum
                _ ≤ (fuel + 1) * (newHeapSize + 2 + 1) := by
                  nlinarith

/-- Top-level heapsort execution paired with build and extraction-step costs. -/
def arrayHeapSortInPlaceWithCost (xs : List Nat) : List Nat × Nat :=
  let built := arrayBuildMaxHeapWithCost xs
  let sorted := arrayHeapSortInPlaceLoopWithCost
    (built.1.length - 1) built.1 built.1.length
  (sorted.1, built.2 + sorted.2)

/-- Erasing the top-level cost recovers the existing in-place heapsort. -/
theorem arrayHeapSortInPlaceWithCost_result (xs : List Nat) :
    (arrayHeapSortInPlaceWithCost xs).1 = arrayHeapSortInPlace xs := by
  unfold arrayHeapSortInPlaceWithCost arrayHeapSortInPlace
  rw [arrayHeapSortInPlaceLoopWithCost_result,
    arrayBuildMaxHeapWithCost_result]

end Chapter06
end CLRS
