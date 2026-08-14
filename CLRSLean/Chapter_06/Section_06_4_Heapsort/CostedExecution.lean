import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import CLRSLean.Chapter_06.Section_06_4_Heapsort

/-!
# Costed execution for CLRS heapsort

This module instruments the executable Chapter 6 heap operations with an
abstract unit control-step count.  Projecting the first component recovers the
existing execution exactly.  The metric counts visited {lit}`MAX-HEAPIFY` frames
and one extraction/swap transition for each nontrivial heapsort step.  Build-
loop orchestration, guards, list reads/writes, allocation, and function calls
are not charged separately; this is not a RAM-cost model for Lean lists.

The tight algorithm-level bounds are proved against this same metric:

- Theorem {lit}`maxHeapifyFuelWithCost_cost_le_height` / {lit}`..._cost_le_log`:
  a heapify run visits at most one frame per level of the repaired subtree, so
  it costs at most {lit}`⌊log₂ heapSize⌋ + 1`.
- Theorem {lit}`buildMaxHeapLoopWithCost_cost_le_linear`: the bottom-up build
  charges at most {lit}`3 · heapSize` steps, via the CLRS double-counting of
  node heights.
- Theorem {lit}`arrayHeapSortInPlaceWithCost_cost_le_log`: the full heapsort
  execution satisfies the {lit}`O(n log n)` envelope {lit}`heapSortNLogNBound`.

Erasure theorems ({lit}`*_result`) show the costed functions project to the
existing executable algorithms.
-/

namespace CLRS
namespace Chapter06

open Chapter03

/-! ## Costed {lit}`MAX-HEAPIFY` -/

/-- {lit}`MAX-HEAPIFY` paired with the number of visited recursive frames. -/
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

/-- The bottom-up build loop uses at most {lit}`count * heapSize` control steps. -/
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

/-- Erasing cost from the costed builder recovers {lit}`arrayBuildMaxHeap`. -/
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

/-- Erasing one costed extraction step recovers {lit}`arrayHeapSortStep`. -/
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

/-- The linear heapify control envelope is {lit}`O(n)`. -/
theorem maxHeapifyControlBound_isBigO_n :
    isBigO (fun n : Nat => (maxHeapifyControlBound n : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨1, by norm_num, 1, fun n _ => ?_⟩
  simp [maxHeapifyControlBound]

/-- The coarse build-heap control envelope is {lit}`O(n²)`. -/
theorem buildMaxHeapControlBound_isBigO_nsq :
    isBigO (fun n : Nat => (buildMaxHeapControlBound n : ℝ))
      (fun n : Nat => (n : ℝ) * n) := by
  rw [isBigO_iff]
  refine ⟨1, by norm_num, 1, fun n _ => ?_⟩
  simp [buildMaxHeapControlBound, Nat.cast_mul]

/-- The coarse heapsort control envelope is {lit}`O(n²)`. -/
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

/-! ## Tight textbook cost bounds

The coarse envelopes above are regression bounds only.  This section charges the
same unit control-step metric (visited {lit}`MAX-HEAPIFY` frames plus one swap
transition per nontrivial heapsort extraction) and proves the tight
algorithm-level bounds: each heapify run is logarithmic in the heap segment, the
bottom-up build is linear in aggregate, and the connected heapsort execution is
{lit}`O(n log n)`.
-/

/-- Height of node `i` in a `heapSize`-cell array heap, bounded by
`⌊log₂ heapSize⌋ - ⌊log₂ (i + 1)⌋`.  A leaf node (no in-heap children) has
height zero. -/
def heapHeight (heapSize i : Nat) : Nat :=
  Nat.log 2 heapSize - Nat.log 2 (i + 1)

/-- Node height never exceeds `⌊log₂ heapSize⌋`. -/
theorem heapHeight_le_log (heapSize i : Nat) :
    heapHeight heapSize i ≤ Nat.log 2 heapSize := by
  simp [heapHeight]

private lemma sub_add_one_le_sub (X Y Z : Nat) (h1 : Y + 1 ≤ Z) (h2 : Z ≤ X) :
    X - Z + 1 ≤ X - Y := by
  omega

/-- Moving from `i` to a child index `j ≥ 2·i + 1` drops the node height by one. -/
theorem heapHeight_child_add_one_le {heapSize i j : Nat}
    (hchild : 2 * i + 1 ≤ j) (hj : j < heapSize) :
    heapHeight heapSize j + 1 ≤ heapHeight heapSize i := by
  have hlog_child : Nat.log 2 (i + 1) + 1 ≤ Nat.log 2 (j + 1) := by
    have hmul : 2 * (i + 1) ≤ j + 1 := by omega
    have hlogmul : Nat.log 2 (2 * (i + 1)) ≤ Nat.log 2 (j + 1) :=
      Nat.log_mono_right hmul
    have hlog2 : Nat.log 2 (2 * (i + 1)) = Nat.log 2 (i + 1) + 1 := by
      rw [Nat.mul_comm 2 (i + 1)]
      exact Nat.log_mul_base (by norm_num) (by omega)
    rwa [hlog2] at hlogmul
  have hlog_le : Nat.log 2 (j + 1) ≤ Nat.log 2 heapSize :=
    Nat.log_mono_right (by omega)
  simpa [heapHeight] using
    sub_add_one_le_sub (Nat.log 2 heapSize) (Nat.log 2 (i + 1)) (Nat.log 2 (j + 1))
      hlog_child hlog_le

/-- A fuelled heapify run visits at most one frame per level of the subtree
rooted at `i`: every swap moves to a child index, which at least doubles
`i + 1`.  This is the CLRS observation that {lit}`MAX-HEAPIFY` runs in time
proportional to the node's height. -/
theorem maxHeapifyFuelWithCost_cost_le_height (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) (hi : i < heapSize) :
    (maxHeapifyFuelWithCost fuel a heapSize i).2 ≤ heapHeight heapSize i + 1 := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuelWithCost]
  | succ fuel ih =>
      simp only [maxHeapifyFuelWithCost]
      split_ifs with hmax
      · omega
      · have hlargest : maxChildIndex a heapSize i < heapSize :=
          maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) (i := i) hi
        have hchild := ih (swapAt a i (maxChildIndex a heapSize i))
          (maxChildIndex a heapSize i) hlargest
        have hge : 2 * i + 1 ≤ maxChildIndex a heapSize i := by
          rcases maxChildIndex_eq_left_or_right_of_ne (a := a) (heapSize := heapSize)
            (i := i) hmax with h | h
          · rw [h]
            unfold left
            omega
          · rw [h]
            unfold right
            omega
        have hdrop := heapHeight_child_add_one_le
          (i := i) (j := maxChildIndex a heapSize i) hge hlargest
        omega

/-- On a valid heap index, a heapify run costs at most `⌊log₂ heapSize⌋ + 1`
control steps.  This is the logarithmic {lit}`MAX-HEAPIFY` bound. -/
theorem maxHeapifyFuelWithCost_cost_le_log (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) (hi : i < heapSize) :
    (maxHeapifyFuelWithCost fuel a heapSize i).2 ≤ Nat.log 2 heapSize + 1 := by
  have h := maxHeapifyFuelWithCost_cost_le_height fuel a heapSize i hi
  exact h.trans (Nat.add_le_add_right (heapHeight_le_log heapSize i) 1)

/-! ## Linear aggregate build bound -/

/-- A level `h` strictly below node `i` witnesses `2 ^ h * (i + 1) ≤ heapSize`. -/
theorem pow_two_mul_le_of_lt_heapHeight {heapSize i h : Nat}
    (hi : i < heapSize) (hlt : h < heapHeight heapSize i) :
    2 ^ h * (i + 1) ≤ heapSize := by
  have hlog_le : Nat.log 2 (i + 1) ≤ Nat.log 2 heapSize :=
    Nat.log_mono_right (by omega)
  have h_add : h + Nat.log 2 (i + 1) < Nat.log 2 heapSize := by
    unfold heapHeight at hlt
    omega
  have hpow_succ : h + Nat.log 2 (i + 1) + 1 ≤ Nat.log 2 heapSize := by omega
  have hself : i + 1 ≤ 2 ^ (Nat.log 2 (i + 1) + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) (i + 1))
  have hmul_le : 2 ^ h * (i + 1) ≤ 2 ^ (h + Nat.log 2 (i + 1) + 1) := by
    calc
      2 ^ h * (i + 1) ≤ 2 ^ h * 2 ^ (Nat.log 2 (i + 1) + 1) :=
        Nat.mul_le_mul_left (2 ^ h) hself
      _ = 2 ^ (h + Nat.log 2 (i + 1) + 1) := by
        rw [← pow_add]
        rfl
  have hpow_n : 2 ^ (h + Nat.log 2 (i + 1) + 1) ≤ heapSize := by
    exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow_succ).trans
      (Nat.pow_log_le_self 2 (by omega : heapSize ≠ 0))
  exact Nat.le_trans hmul_le hpow_n

/-- Every node of height exceeding `h` lies below index `heapSize / 2 ^ h`. -/
theorem mem_range_div_pow_of_lt_heapHeight {heapSize i h : Nat}
    (hi : i < heapSize) (hlt : h < heapHeight heapSize i) :
    i < heapSize / 2 ^ h := by
  have hpow := pow_two_mul_le_of_lt_heapHeight hi hlt
  have hi1 : i + 1 ≤ heapSize / 2 ^ h := by
    rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by norm_num))]
    rwa [Nat.mul_comm]
  omega

/-- At most `heapSize / 2 ^ h` nodes have height strictly exceeding `h`. -/
theorem card_lt_heapHeight_le (heapSize h : Nat) :
    ({i ∈ Finset.range heapSize | h < heapHeight heapSize i}.card) ≤
      heapSize / 2 ^ h := by
  have hsub : {i ∈ Finset.range heapSize | h < heapHeight heapSize i} ⊆
      Finset.range (heapSize / 2 ^ h) := by
    intro i hi
    have hi' : i < heapSize := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hlt : h < heapHeight heapSize i := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (mem_range_div_pow_of_lt_heapHeight hi' hlt)
  simpa [Finset.card_range] using Finset.card_le_card hsub

/-- A node's height is the number of levels strictly below it. -/
theorem heapHeight_eq_sum_levels (heapSize i : Nat) :
    heapHeight heapSize i =
      ∑ h ∈ Finset.range (Nat.log 2 heapSize + 1),
        if h < heapHeight heapSize i then 1 else 0 := by
  rw [← Finset.card_filter (fun h => h < heapHeight heapSize i)
    (Finset.range (Nat.log 2 heapSize + 1))]
  have hfilter : {h ∈ Finset.range (Nat.log 2 heapSize + 1) |
        h < heapHeight heapSize i} =
      Finset.range (heapHeight heapSize i) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hmem
      exact hmem.2
    · intro hlt
      have hle := heapHeight_le_log heapSize i
      exact ⟨Nat.lt_of_lt_of_le hlt (by omega), hlt⟩
  rw [hfilter, Finset.card_range]

private lemma sub_add_le_sub_of_two_add_le (a x y : Nat) (hy : y ≤ a) (hxy : x + x ≤ y) :
    (a - y) + x ≤ a - x := by
  omega

/-- Geometric tail: `Σ_{h < m} heapSize / 2 ^ h ≤ 2 * heapSize`. -/
theorem sum_div_pow_two_le (heapSize m : Nat) :
    (∑ h ∈ Finset.range m, heapSize / 2 ^ h) ≤ 2 * heapSize := by
  cases m with
  | zero =>
      simp
  | succ k =>
      have hstrong :
          (∑ h ∈ Finset.range (k + 1), heapSize / 2 ^ h) ≤
            2 * heapSize - heapSize / 2 ^ k := by
        induction k with
        | zero =>
            simp
            omega
        | succ k ih =>
            rw [Finset.sum_range_succ]
            have hle :
                heapSize / 2 ^ (k + 1) + heapSize / 2 ^ (k + 1) ≤
                  heapSize / 2 ^ k := by
              have hdiv : heapSize / 2 ^ (k + 1) = heapSize / 2 ^ k / 2 := by
                rw [pow_succ]
                rw [Nat.div_div_eq_div_mul]
              rw [hdiv]
              simpa [two_mul] using Nat.mul_div_le (heapSize / 2 ^ k) 2
            calc
              (∑ h ∈ Finset.range (k + 1), heapSize / 2 ^ h) +
                  heapSize / 2 ^ (k + 1) ≤
                  (2 * heapSize - heapSize / 2 ^ k) + heapSize / 2 ^ (k + 1) :=
                Nat.add_le_add_right ih _
              _ ≤ 2 * heapSize - heapSize / 2 ^ (k + 1) := by
                have hy : heapSize / 2 ^ k ≤ 2 * heapSize :=
                  Nat.le_trans (Nat.div_le_self heapSize (2 ^ k)) (by omega)
                exact sub_add_le_sub_of_two_add_le (2 * heapSize)
                  (heapSize / 2 ^ (k + 1)) (heapSize / 2 ^ k) hy hle
      exact hstrong.trans (Nat.sub_le (2 * heapSize) (heapSize / 2 ^ k))

/-- Summing node heights over a heap is at most `2 * heapSize` (the CLRS
double-counting argument for linear {lit}`BUILD-MAX-HEAP`). -/
theorem sum_heapHeight_le (heapSize : Nat) :
    (∑ i ∈ Finset.range heapSize, heapHeight heapSize i) ≤ 2 * heapSize := by
  calc
    (∑ i ∈ Finset.range heapSize, heapHeight heapSize i)
        = ∑ i ∈ Finset.range heapSize,
            ∑ h ∈ Finset.range (Nat.log 2 heapSize + 1),
              if h < heapHeight heapSize i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact heapHeight_eq_sum_levels heapSize i
    _ = ∑ h ∈ Finset.range (Nat.log 2 heapSize + 1),
            ∑ i ∈ Finset.range heapSize,
              if h < heapHeight heapSize i then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ h ∈ Finset.range (Nat.log 2 heapSize + 1),
            ({i ∈ Finset.range heapSize | h < heapHeight heapSize i}.card) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact (Finset.card_filter (fun i => h < heapHeight heapSize i)
            (Finset.range heapSize)).symm
    _ ≤ ∑ h ∈ Finset.range (Nat.log 2 heapSize + 1), heapSize / 2 ^ h := by
          apply Finset.sum_le_sum
          intro h hh
          exact card_lt_heapHeight_le heapSize h
    _ ≤ 2 * heapSize := sum_div_pow_two_le heapSize (Nat.log 2 heapSize + 1)

/-- The bottom-up build loop's cost is the sum of per-node heapify costs. -/
theorem buildMaxHeapLoopWithCost_cost_le_height_sum (count : Nat) (a : List Nat)
    (heapSize : Nat) (hcount : count ≤ heapSize) :
    (buildMaxHeapLoopWithCost count a heapSize).2 ≤
      ∑ j ∈ Finset.range count, (heapHeight heapSize j + 1) := by
  induction count generalizing a with
  | zero =>
      simp [buildMaxHeapLoopWithCost]
  | succ count ih =>
      simp only [buildMaxHeapLoopWithCost]
      have hrepair : (maxHeapifyFuelWithCost heapSize a heapSize count).2 ≤
          heapHeight heapSize count + 1 :=
        maxHeapifyFuelWithCost_cost_le_height heapSize a heapSize count (by omega)
      have hrest := ih (maxHeapifyFuelWithCost heapSize a heapSize count).1 (by omega)
      rw [Finset.sum_range_succ]
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
        Nat.add_le_add hrepair hrest

/-- Restricting the per-node height sum to a shorter prefix only decreases it. -/
theorem sum_heapHeight_range_mono {n m : Nat} (h : n ≤ m) :
    (∑ j ∈ Finset.range n, (heapHeight m j + 1)) ≤
      ∑ j ∈ Finset.range m, (heapHeight m j + 1) := by
  have hsub : Finset.range n ⊆ Finset.range m := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x hx2 hx1; omega)

/-- Bottom-up heap construction charges at most `3 * heapSize` control steps. -/
theorem buildMaxHeapLoopWithCost_cost_le_linear (count : Nat) (a : List Nat)
    (heapSize : Nat) (hcount : count ≤ heapSize) :
    (buildMaxHeapLoopWithCost count a heapSize).2 ≤ 3 * heapSize := by
  have hsum := buildMaxHeapLoopWithCost_cost_le_height_sum count a heapSize hcount
  have hsum_sub := sum_heapHeight_range_mono (n := count) (m := heapSize) hcount
  have htotal :
      (∑ j ∈ Finset.range heapSize, (heapHeight heapSize j + 1)) ≤ 3 * heapSize := by
    calc
      (∑ j ∈ Finset.range heapSize, (heapHeight heapSize j + 1))
          = (∑ j ∈ Finset.range heapSize, heapHeight heapSize j) + heapSize := by
            rw [Finset.sum_add_distrib]
            simp [Finset.card_range]
      _ ≤ 2 * heapSize + heapSize := Nat.add_le_add_right (sum_heapHeight_le heapSize) heapSize
      _ = 3 * heapSize := by omega
  exact hsum.trans (hsum_sub.trans htotal)

/-- Named linear envelope for bottom-up heap construction. -/
def buildMaxHeapLinearBound (n : Nat) : Nat := 3 * n

/-- The costed builder satisfies the named linear envelope. -/
theorem arrayBuildMaxHeapWithCost_cost_le_linear (xs : List Nat) :
    (arrayBuildMaxHeapWithCost xs).2 ≤ buildMaxHeapLinearBound xs.length := by
  unfold arrayBuildMaxHeapWithCost buildMaxHeapLinearBound
  exact buildMaxHeapLoopWithCost_cost_le_linear (xs.length / 2) xs xs.length
    (Nat.div_le_self xs.length 2)

/-! ## {lit}`O(n log n)` heapsort bound -/

/-- A single extraction step costs at most `⌊log₂ heapSize⌋ + 2` control steps. -/
theorem arrayHeapSortStepWithCost_cost_le_log (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortStepWithCost a heapSize).2 ≤ Nat.log 2 heapSize + 2 := by
  cases heapSize with
  | zero =>
      simp [arrayHeapSortStepWithCost]
  | succ heapSize =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortStepWithCost]
      | succ newHeapSize =>
          have hh := maxHeapifyFuelWithCost_cost_le_log (newHeapSize + 1)
            (swapAt a 0 (newHeapSize + 1)) (newHeapSize + 1) 0 (by omega)
          have hmono : Nat.log 2 (newHeapSize + 1) ≤ Nat.log 2 (newHeapSize + 2) :=
            Nat.log_mono_right (by omega)
          simpa [arrayHeapSortStepWithCost] using
            (calc
              (maxHeapifyFuelWithCost (newHeapSize + 1) (swapAt a 0 (newHeapSize + 1))
                (newHeapSize + 1) 0).2 + 1 ≤
                  (Nat.log 2 (newHeapSize + 1) + 1) + 1 := Nat.add_le_add_right hh 1
              _ = Nat.log 2 (newHeapSize + 1) + 2 := by omega
              _ ≤ Nat.log 2 (newHeapSize + 2) + 2 := Nat.add_le_add_right hmono 2)

/-- The shrinking heapsort loop charges at most `fuel * (⌊log₂ heapSize⌋ + 2)`
control steps. -/
theorem arrayHeapSortInPlaceLoopWithCost_cost_le_log (fuel : Nat) (a : List Nat)
    (heapSize : Nat) :
    (arrayHeapSortInPlaceLoopWithCost fuel a heapSize).2 ≤
      fuel * (Nat.log 2 heapSize + 2) := by
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
              have hstep := arrayHeapSortStepWithCost_cost_le_log a (newHeapSize + 2)
              have hrest := ih (arrayHeapSortStepWithCost a (newHeapSize + 2)).1
                (newHeapSize + 1)
              have hmono : Nat.log 2 (newHeapSize + 1) + 2 ≤ Nat.log 2 (newHeapSize + 2) + 2 :=
                Nat.add_le_add_right (Nat.log_mono_right (by omega)) 2
              have hrest' :
                  (arrayHeapSortInPlaceLoopWithCost fuel
                    (arrayHeapSortStepWithCost a (newHeapSize + 2)).1
                    (newHeapSize + 1)).2 ≤
                    fuel * (Nat.log 2 (newHeapSize + 2) + 2) :=
                hrest.trans (Nat.mul_le_mul_left fuel hmono)
              calc
                (arrayHeapSortStepWithCost a (newHeapSize + 2)).2 +
                    (arrayHeapSortInPlaceLoopWithCost fuel
                      (arrayHeapSortStepWithCost a (newHeapSize + 2)).1
                      (newHeapSize + 1)).2 ≤
                    (Nat.log 2 (newHeapSize + 2) + 2) +
                      fuel * (Nat.log 2 (newHeapSize + 2) + 2) :=
                  Nat.add_le_add hstep hrest'
                _ = (fuel + 1) * (Nat.log 2 (newHeapSize + 2) + 2) := by
                  ring

/-- Named `O(n log n)` envelope for the full costed heapsort execution. -/
def heapSortNLogNBound (n : Nat) : Nat := n * Nat.log 2 n + 5 * n

/-- The full costed heapsort run satisfies the named {lit}`O(n log n)` envelope. -/
theorem arrayHeapSortInPlaceWithCost_cost_le_log (xs : List Nat) :
    (arrayHeapSortInPlaceWithCost xs).2 ≤ heapSortNLogNBound xs.length := by
  let built := arrayBuildMaxHeapWithCost xs
  have hbuiltLength : built.1.length = xs.length := by
    rw [show built.1 = arrayBuildMaxHeap xs by
      simpa [built] using arrayBuildMaxHeapWithCost_result xs]
    exact (arrayBuildMaxHeap_correct xs).2.2
  have hbuild : built.2 ≤ 3 * xs.length := by
    simpa [built, buildMaxHeapLinearBound] using arrayBuildMaxHeapWithCost_cost_le_linear xs
  have hloopRaw := arrayHeapSortInPlaceLoopWithCost_cost_le_log
    (built.1.length - 1) built.1 built.1.length
  have hloop :
      (arrayHeapSortInPlaceLoopWithCost (built.1.length - 1) built.1 built.1.length).2 ≤
        xs.length * (Nat.log 2 xs.length + 2) := by
    calc
      (arrayHeapSortInPlaceLoopWithCost (built.1.length - 1) built.1 built.1.length).2 ≤
          (built.1.length - 1) * (Nat.log 2 built.1.length + 2) := hloopRaw
      _ = (xs.length - 1) * (Nat.log 2 xs.length + 2) := by rw [hbuiltLength]
      _ ≤ xs.length * (Nat.log 2 xs.length + 2) :=
        Nat.mul_le_mul_right (Nat.log 2 xs.length + 2) (Nat.sub_le xs.length 1)
  unfold arrayHeapSortInPlaceWithCost
  change built.2 +
      (arrayHeapSortInPlaceLoopWithCost (built.1.length - 1) built.1 built.1.length).2 ≤
      heapSortNLogNBound xs.length
  calc
    built.2 +
        (arrayHeapSortInPlaceLoopWithCost (built.1.length - 1) built.1 built.1.length).2 ≤
        3 * xs.length + xs.length * (Nat.log 2 xs.length + 2) :=
      Nat.add_le_add hbuild hloop
    _ = heapSortNLogNBound xs.length := by
      unfold heapSortNLogNBound
      ring

/-- Sortedness, permutation, and the tight {lit}`O(n log n)` envelope together. -/
theorem arrayHeapSortInPlaceWithCost_correct_and_log_cost (xs : List Nat) :
    OrderedAsc (arrayHeapSortInPlaceWithCost xs).1 ∧
      (arrayHeapSortInPlaceWithCost xs).1.Perm xs ∧
      (arrayHeapSortInPlaceWithCost xs).2 ≤ heapSortNLogNBound xs.length := by
  rw [arrayHeapSortInPlaceWithCost_result]
  exact ⟨arrayHeapSortInPlace_orderedAsc xs,
    arrayHeapSortInPlace_perm xs, arrayHeapSortInPlaceWithCost_cost_le_log xs⟩

/-! ## Honest asymptotic wrappers for the tight bounds -/

/-- Named `O(log n)` envelope for a root {lit}`MAX-HEAPIFY` run. -/
def maxHeapifyLogBound (n : Nat) : Nat := Nat.log 2 n + 1

/-- The logarithmic heapify envelope is {lit}`O(log n)`. -/
theorem maxHeapifyLogBound_isBigO_log :
    isBigO (fun n : Nat => (maxHeapifyLogBound n : ℝ))
      (fun n : Nat => (Nat.log 2 n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨2, by norm_num, 2, fun n hn => ?_⟩
  have hnlog : 1 ≤ Nat.log 2 n :=
    Nat.log_pos (by norm_num : 1 < 2) (by omega : 2 ≤ n)
  simp only [maxHeapifyLogBound, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.log 2 n : ℝ) + 1),
    abs_of_nonneg (by positivity : 0 ≤ (Nat.log 2 n : ℝ))]
  have hnat : Nat.log 2 n + 1 ≤ 2 * Nat.log 2 n := by omega
  exact_mod_cast hnat

/-- The linear build-heap envelope is {lit}`O(n)`. -/
theorem buildMaxHeapLinearBound_isBigO_n :
    isBigO (fun n : Nat => (buildMaxHeapLinearBound n : ℝ))
      (fun n : Nat => (n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨3, by norm_num, 0, fun n _ => ?_⟩
  simp [buildMaxHeapLinearBound, Nat.cast_mul, abs_of_nonneg]

/-- The {lit}`O(n log n)` heapsort envelope is indeed {lit}`O(n log n)`. -/
theorem heapSortNLogNBound_isBigO_nlogn :
    isBigO (fun n : Nat => (heapSortNLogNBound n : ℝ))
      (fun n : Nat => (n : ℝ) * (Nat.log 2 n : ℝ)) := by
  rw [isBigO_iff]
  refine ⟨6, by norm_num, 2, fun n hn => ?_⟩
  have hlog : (1 : ℝ) ≤ (Nat.log 2 n : ℝ) := by
    exact_mod_cast (Nat.log_pos (by norm_num : 1 < 2) (by omega : 2 ≤ n))
  simp only [heapSortNLogNBound, Nat.cast_add, Nat.cast_mul]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hn' : (0 : ℝ) ≤ n := by positivity
  have hmul : (n : ℝ) ≤ (n : ℝ) * (Nat.log 2 n : ℝ) := by
    calc
      (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (Nat.log 2 n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hlog hn'
      _ = (n : ℝ) * (Nat.log 2 n : ℝ) := by ring
  have h5 : 5 * (n : ℝ) ≤ 5 * ((n : ℝ) * (Nat.log 2 n : ℝ)) :=
    mul_le_mul_of_nonneg_left hmul (by norm_num)
  calc
    (n : ℝ) * (Nat.log 2 n : ℝ) + 5 * (n : ℝ) ≤
        (n : ℝ) * (Nat.log 2 n : ℝ) + 5 * ((n : ℝ) * (Nat.log 2 n : ℝ)) :=
      add_le_add_right h5 ((n : ℝ) * (Nat.log 2 n : ℝ))
    _ = 6 * ((n : ℝ) * (Nat.log 2 n : ℝ)) := by ring

end Chapter06
end CLRS
