import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues.Insert.Checked

/-!
# Section 6.5 — Costed MAX-HEAP-INSERT

This module charges one unit for every visited nonempty-fuel frame of the
upward-bubbling controller.  Reads, writes, list insertion, allocation, and
guards are not separately charged, matching Chapter 6's existing abstract
unit-control-step metric rather than claiming RAM costs for Lean lists.
-/

namespace CLRS
namespace Chapter06

/-- Upward bubbling paired with its number of visited control frames. -/
def arrayHeapIncreaseKeyBubbleUpFuelWithCost :
    Nat → List Nat → Nat → Nat → List Nat × Nat
  | 0, a, _heapSize, _i => (a, 0)
  | fuel + 1, a, heapSize, i =>
      if _ : 0 < i then
        if valAt a (parent i) < valAt a i then
          let next := arrayHeapIncreaseKeyBubbleUpFuelWithCost fuel
            (swapAt a i (parent i)) heapSize (parent i)
          (next.1, next.2 + 1)
        else
          (a, 1)
      else
        (a, 1)

/-- Erasing the cost recovers the existing upward-bubbling implementation. -/
theorem arrayHeapIncreaseKeyBubbleUpFuelWithCost_result
    (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (arrayHeapIncreaseKeyBubbleUpFuelWithCost fuel a heapSize i).1 =
      arrayHeapIncreaseKeyBubbleUpFuel fuel a heapSize i := by
  induction fuel generalizing a i with
  | zero =>
      simp [arrayHeapIncreaseKeyBubbleUpFuelWithCost,
        arrayHeapIncreaseKeyBubbleUpFuel]
  | succ fuel ih =>
      simp only [arrayHeapIncreaseKeyBubbleUpFuelWithCost,
        arrayHeapIncreaseKeyBubbleUpFuel]
      split_ifs
      · exact ih _ _
      · rfl
      · rfl

/-- A zero-based heap parent step drops the binary index level by at least one. -/
theorem parent_log_add_one_le {i : Nat} (hpos : 0 < i) :
    Nat.log 2 (parent i + 1) + 1 ≤ Nat.log 2 (i + 1) := by
  have hmul : 2 * (parent i + 1) ≤ i + 1 := by
    rcases eq_left_or_right_parent hpos with hleft | hright
    · unfold left at hleft
      omega
    · unfold right at hright
      omega
  have hmono : Nat.log 2 (2 * (parent i + 1)) ≤ Nat.log 2 (i + 1) :=
    Nat.log_mono_right hmul
  have hlogmul :
      Nat.log 2 (2 * (parent i + 1)) = Nat.log 2 (parent i + 1) + 1 := by
    rw [Nat.mul_comm 2 (parent i + 1)]
    exact Nat.log_mul_base (by norm_num) (by omega)
  rwa [hlogmul] at hmono

/--
Upward bubbling visits at most one frame per binary-index level, including its
terminal frame.
-/
theorem arrayHeapIncreaseKeyBubbleUpFuelWithCost_cost_le_log
    (fuel : Nat) (a : List Nat) (heapSize i : Nat) :
    (arrayHeapIncreaseKeyBubbleUpFuelWithCost fuel a heapSize i).2 ≤
      Nat.log 2 (i + 1) + 1 := by
  induction fuel generalizing a i with
  | zero =>
      simp [arrayHeapIncreaseKeyBubbleUpFuelWithCost]
  | succ fuel ih =>
      simp only [arrayHeapIncreaseKeyBubbleUpFuelWithCost]
      split_ifs with hpos hswap
      · have hrec := ih (swapAt a i (parent i)) (parent i)
        have hdrop := parent_log_add_one_le hpos
        omega
      · simp
      · simp

/-- Full-prefix insertion paired with upward-bubbling control cost. -/
def arrayHeapInsertWithCost (a : List Nat) (key : Nat) : List Nat × Nat :=
  arrayHeapIncreaseKeyBubbleUpFuelWithCost a.length (a ++ [key])
    (a.length + 1) a.length

/-- Erasing full-prefix insertion cost recovers `arrayHeapInsert`. -/
theorem arrayHeapInsertWithCost_result (a : List Nat) (key : Nat) :
    (arrayHeapInsertWithCost a key).1 = arrayHeapInsert a key := by
  exact arrayHeapIncreaseKeyBubbleUpFuelWithCost_result
    a.length (a ++ [key]) (a.length + 1) a.length

/-- Full-prefix insertion has an explicit logarithmic control-frame bound. -/
theorem arrayHeapInsertWithCost_cost_le_log (a : List Nat) (key : Nat) :
    (arrayHeapInsertWithCost a key).2 ≤ Nat.log 2 (a.length + 1) + 1 := by
  exact arrayHeapIncreaseKeyBubbleUpFuelWithCost_cost_le_log
    a.length (a ++ [key]) (a.length + 1) a.length

/-- Checked active-prefix insertion with its upward-bubbling control cost. -/
def arrayHeapInsertWithCost? (a : List Nat) (heapSize key : Nat) :
    Option ((List Nat × Nat) × Nat) :=
  if _h : heapSize ≤ a.length then
    let run := arrayHeapInsertWithCost (a.take heapSize) key
    some ((run.1 ++ a.drop heapSize, heapSize + 1), run.2)
  else
    none

/-- Erasing checked insertion cost recovers the checked state operation. -/
theorem arrayHeapInsertWithCost?_result (a : List Nat) (heapSize key : Nat) :
    (arrayHeapInsertWithCost? a heapSize key).map Prod.fst =
      arrayHeapInsert? a heapSize key := by
  unfold arrayHeapInsertWithCost? arrayHeapInsert?
  by_cases h : heapSize ≤ a.length
  · simp [h, arrayHeapInsertWithCost_result]
  · simp [h]

/--
The checked costed wrapper inherits the complete state contract and the
logarithmic bound in the enlarged heap size.
-/
theorem arrayHeapInsertWithCost?_state_correct_and_log_cost
    {a rest : List Nat} {heapSize newHeapSize key cost : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapInsertWithCost? a heapSize key =
      some ((rest, newHeapSize), cost)) :
    heapSize ≤ a.length ∧
      newHeapSize = heapSize + 1 ∧
      rest.length = a.length + 1 ∧
      ArrayMaxHeap rest newHeapSize ∧
      rest.Perm (key :: a) ∧
      rest.drop newHeapSize = a.drop heapSize ∧
      cost ≤ Nat.log 2 newHeapSize + 1 := by
  have hraw : arrayHeapInsert? a heapSize key = some (rest, newHeapSize) := by
    have hmap := congrArg (Option.map Prod.fst) hres
    rw [arrayHeapInsertWithCost?_result] at hmap
    simpa using hmap
  have hstate := arrayHeapInsert?_state_correct hheap hraw
  rcases hstate with ⟨hguard, hsize, hlength, hresultHeap, hperm, htail⟩
  have hcostRun := arrayHeapInsertWithCost_cost_le_log (a.take heapSize) key
  have htakeLen : (a.take heapSize).length = heapSize :=
    List.length_take_of_le hguard
  have hcost : cost = (arrayHeapInsertWithCost (a.take heapSize) key).2 := by
    unfold arrayHeapInsertWithCost? at hres
    rw [dif_pos hguard] at hres
    have hall :
        (rest = (arrayHeapInsertWithCost (a.take heapSize) key).1 ++ a.drop heapSize ∧
          newHeapSize = heapSize + 1) ∧
          cost = (arrayHeapInsertWithCost (a.take heapSize) key).2 := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hres.symm
    exact hall.2
  refine ⟨hguard, hsize, hlength, hresultHeap, hperm, htail, ?_⟩
  rw [hcost, hsize]
  simpa [htakeLen] using hcostRun

end Chapter06
end CLRS
