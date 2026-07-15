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
      simp [arrayHeapSortStepWithCost]
  | succ heapSize =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortStepWithCost]
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

/-! ## Concrete control-step envelopes -/

/-- Linear envelope for the visited frames of one fuelled heapify run. -/
def maxHeapifyControlBound (n : Nat) : Nat := n

/-- Coarse quadratic envelope for bottom-up heap construction. -/
def buildMaxHeapControlBound (n : Nat) : Nat := n * n

/-- Coarse quadratic envelope for heap construction plus all extraction steps. -/
def heapSortControlBound (n : Nat) : Nat := 2 * n * n + n

/-- The fuel bound on heapify is exactly its named linear envelope. -/
theorem maxHeapifyFuelWithCost_cost_le_controlBound
    (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (maxHeapifyFuelWithCost fuel a heapSize i).2 ≤
      maxHeapifyControlBound fuel := by
  simpa [maxHeapifyControlBound] using
    maxHeapifyFuelWithCost_cost_le_fuel fuel a heapSize i

/-- A costed bottom-up build is bounded by the named quadratic envelope. -/
theorem arrayBuildMaxHeapWithCost_cost_le (xs : List Nat) :
    (arrayBuildMaxHeapWithCost xs).2 ≤
      buildMaxHeapControlBound xs.length := by
  unfold arrayBuildMaxHeapWithCost buildMaxHeapControlBound
  exact (buildMaxHeapLoopWithCost_cost_le
    (xs.length / 2) xs xs.length).trans
      (Nat.mul_le_mul_right xs.length (Nat.div_le_self xs.length 2))

/-- A full costed heapsort run is bounded by the named quadratic envelope. -/
theorem arrayHeapSortInPlaceWithCost_cost_le (xs : List Nat) :
    (arrayHeapSortInPlaceWithCost xs).2 ≤ heapSortControlBound xs.length := by
  let built := arrayBuildMaxHeapWithCost xs
  have hbuiltLength : built.1.length = xs.length := by
    rw [show built.1 = arrayBuildMaxHeap xs by
      simpa [built] using arrayBuildMaxHeapWithCost_result xs]
    exact (arrayBuildMaxHeap_correct xs).2.2
  have hbuild : built.2 ≤ xs.length * xs.length := by
    simpa [built, buildMaxHeapControlBound] using
      arrayBuildMaxHeapWithCost_cost_le xs
  have hloopRaw := arrayHeapSortInPlaceLoopWithCost_cost_le
    (built.1.length - 1) built.1 built.1.length
  have hloop :
      (arrayHeapSortInPlaceLoopWithCost
        (built.1.length - 1) built.1 built.1.length).2 ≤
        xs.length * (xs.length + 1) := by
    calc
      (arrayHeapSortInPlaceLoopWithCost
          (built.1.length - 1) built.1 built.1.length).2 ≤
          (built.1.length - 1) * (built.1.length + 1) := hloopRaw
      _ = (xs.length - 1) * (xs.length + 1) := by rw [hbuiltLength]
      _ ≤ xs.length * (xs.length + 1) :=
        Nat.mul_le_mul_right (xs.length + 1) (Nat.sub_le xs.length 1)
  unfold arrayHeapSortInPlaceWithCost
  change built.2 +
      (arrayHeapSortInPlaceLoopWithCost
        (built.1.length - 1) built.1 built.1.length).2 ≤
      heapSortControlBound xs.length
  calc
    built.2 +
        (arrayHeapSortInPlaceLoopWithCost
          (built.1.length - 1) built.1 built.1.length).2 ≤
        xs.length * xs.length + xs.length * (xs.length + 1) :=
      Nat.add_le_add hbuild hloop
    _ = heapSortControlBound xs.length := by
      unfold heapSortControlBound
      ring

/-- The costed run is a sorted permutation and satisfies its concrete envelope. -/
theorem arrayHeapSortInPlaceWithCost_correct_and_cost (xs : List Nat) :
    OrderedAsc (arrayHeapSortInPlaceWithCost xs).1 ∧
      (arrayHeapSortInPlaceWithCost xs).1.Perm xs ∧
      (arrayHeapSortInPlaceWithCost xs).2 ≤ heapSortControlBound xs.length := by
  rw [arrayHeapSortInPlaceWithCost_result]
  exact ⟨arrayHeapSortInPlace_orderedAsc xs,
    arrayHeapSortInPlace_perm xs, arrayHeapSortInPlaceWithCost_cost_le xs⟩

/-! ## Honest asymptotic wrappers for the coarse envelopes -/

/-- The linear heapify control envelope is `O(n)`. -/
theorem maxHeapifyControlBound_isBigO_n :
    isBigO (fun n : Nat => (maxHeapifyControlBound n : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨1, by norm_num, 1, fun n _ => ?_⟩
  simp [maxHeapifyControlBound]

/-- The coarse build-heap control envelope is `O(n²)`. -/
theorem buildMaxHeapControlBound_isBigO_nsq :
    isBigO (fun n : Nat => (buildMaxHeapControlBound n : ℝ))
      (fun n : Nat => (n : ℝ) * n) := by
  rw [isBigO_iff]
  refine ⟨1, by norm_num, 1, fun n _ => ?_⟩
  simp [buildMaxHeapControlBound, Nat.cast_mul]

/-- The coarse heapsort control envelope is `O(n²)`. -/
theorem heapSortControlBound_isBigO_nsq :
    isBigO (fun n : Nat => (heapSortControlBound n : ℝ))
      (fun n : Nat => (n : ℝ) * n) := by
  rw [isBigO_iff]
  refine ⟨3, by norm_num, 1, fun n hn => ?_⟩
  simp only [heapSortControlBound, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnNonneg : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_nonneg hnNonneg (sub_nonneg.mpr hnReal)]

end Chapter06
end CLRS
