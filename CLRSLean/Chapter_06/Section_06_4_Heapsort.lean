import CLRSLean.Chapter_06.Section_06_3_Building_A_Heap

/-!
# CLRS Section 6.4 - The Heapsort Algorithm

This section gives the array-level refinement of CLRS {lit}`HEAPSORT`.  The
older functional heapsort theorem is kept as a compact auxiliary scaffold, but
the reader-facing theorem now follows the in-place loop shape directly:
swap the heap root with the last heap element, shrink the heap prefix, then
repair the prefix with {lit}`MAX-HEAPIFY`.

Main results:

- Definition {lit}`arrayHeapSortInPlaceLoop`: the CLRS shrinking-heap loop.
- Theorem {lit}`arrayHeapSortInPlaceLoop_perm`: the loop preserves the multiset
  of array elements.
- Theorem {lit}`arrayHeapSortInPlaceLoop_length`: the loop preserves array
  length.
- Definitions {lit}`SortedSuffix`, {lit}`PrefixLeSuffix`, and
  {lit}`HeapSortLoopInvariant`: the formal sorted-suffix loop invariant.
- Theorems {lit}`arrayHeapSortStep_suffix_head_eq_root` and
  {lit}`arrayHeapSortStep_suffix_head_bounds_prefix`: one CLRS iteration moves
  the old heap root to the new sorted-suffix head and leaves it above the
  remaining heap prefix.
- Theorem {lit}`HeapSortLoopInvariant.step`: one nontrivial CLRS loop iteration
  preserves the full heap-prefix / sorted-suffix invariant.
- Theorem {lit}`arrayHeapSortStep_state_correct`: one nontrivial CLRS iteration
  bundles the next invariant, permutation, length preservation, and root-to-
  suffix-head fact.
- Theorem {lit}`arrayHeapSortInPlaceLoop_exact_shrink_invariant`: after any
  admissible number of iterations, the heap prefix has exactly shrunk by that
  many cells.
- Theorem {lit}`arrayHeapSortInPlaceLoop_terminal_invariant`: repeated loop
  iterations preserve the invariant until the heap prefix has size at most one.
- Theorem {lit}`arrayHeapSortInPlaceLoop_orderedAsc`: the fuelled in-place loop
  returns ascending output when started with enough fuel and the invariant.
- Theorem {lit}`arrayHeapSortInPlaceLoop_state_correct`: the same loop also
  exposes the final terminal invariant, sortedness, permutation, and length
  preservation as one CLRS-style state-correctness package.
- Theorem {lit}`arrayHeapSortInPlaceLoop_exact_state_correct`: the exact
  partial-run invariant together with permutation and length preservation.
- Theorem {lit}`arrayHeapSortInPlace_orderedAsc`: the CLRS in-place heapsort
  implementation returns ascending output.
- Theorems {lit}`arrayHeapSortInPlace_exact_state_correct` and
  {lit}`arrayHeapSort_exact_state_correct`: non-existential exact terminal
  state packages for the in-place and public heapsort interfaces.
- Theorem {lit}`arrayHeapSort_orderedAsc`: heapsort returns ascending output.
- Theorem {lit}`arrayHeapSort_perm`: heapsort preserves the multiset of input
  elements.
- Theorems {lit}`arrayHeapSortInPlace_correct` and
  {lit}`arrayHeapSort_correct`: reader-facing correctness specifications
  bundling sortedness, permutation, and length preservation.

Remaining refinements:

- The in-place correctness proof is complete at the current functional-array
  level.  Later work can add line-by-line RAM costs and share an imperative
  array semantics with other chapters.
-/

namespace CLRS
namespace Chapter06

/-! ## In-place heapsort loop scaffold -/

/--
The suffix from {lit}`heapSize` to the end of the array is sorted in ascending
order.  The predicate is stated with {lit}`valAt` to keep later swap and heapify
proofs free of repetitive in-bounds casts.
-/
def SortedSuffix (a : List Nat) (heapSize : Nat) : Prop :=
  ∀ {i j : Nat}, heapSize ≤ i → i ≤ j → j < a.length → valAt a i ≤ valAt a j

/--
Every element in the heap prefix is at most every element in the sorted suffix.
Together with {lit}`ArrayMaxHeap` on the prefix, this is the usual CLRS loop
invariant for heapsort.
-/
def PrefixLeSuffix (a : List Nat) (heapSize : Nat) : Prop :=
  ∀ {i j : Nat}, i < heapSize → heapSize ≤ j → j < a.length → valAt a i ≤ valAt a j

/-- Every element in the heap prefix is bounded by a fixed value. -/
def PrefixLeBound (a : List Nat) (heapSize bound : Nat) : Prop :=
  ∀ {i : Nat}, i < heapSize → valAt a i ≤ bound

/-- The array-level CLRS heapsort loop invariant. -/
structure HeapSortLoopInvariant (a : List Nat) (heapSize : Nat) : Prop where
  heap : ArrayMaxHeap a heapSize
  suffix_sorted : SortedSuffix a heapSize
  prefix_le_suffix : PrefixLeSuffix a heapSize

/-- In a nonempty array heap, the root bounds every heap-prefix cell in {lit}`valAt` form. -/
theorem ArrayMaxHeap.valAt_le_root {a : List Nat} {heapSize i : Nat}
    (hheap : ArrayMaxHeap a heapSize) (hi : i < heapSize) :
    valAt a i ≤ valAt a 0 := by
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hheap.heapSize_le_length
  have h0_heap : 0 < heapSize := Nat.zero_lt_of_lt hi
  have h0_len : 0 < a.length := Nat.lt_of_lt_of_le h0_heap hheap.heapSize_le_length
  have hval := hheap.getElem_le_root hi
  rw [← valAt_eq_getElem a hi_len, ← valAt_eq_getElem a h0_len] at hval
  exact hval

/-- The heap root is a bound for the whole heap prefix. -/
theorem PrefixLeBound.of_heap_root {a : List Nat} {heapSize : Nat}
    (hheap : ArrayMaxHeap a heapSize) :
    PrefixLeBound a heapSize (valAt a 0) := by
  intro i hi
  exact hheap.valAt_le_root hi

/-- Swapping two in-prefix cells preserves a prefix-wide upper bound. -/
theorem PrefixLeBound.of_swapAt {a : List Nat} {heapSize bound i j : Nat}
    (hbound : PrefixLeBound a heapSize bound) (hlen : heapSize ≤ a.length)
    (hi : i < heapSize) (hj : j < heapSize) :
    PrefixLeBound (swapAt a i j) heapSize bound := by
  intro k hk
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hlen
  have hj_len : j < a.length := Nat.lt_of_lt_of_le hj hlen
  by_cases hki : k = i
  · subst k
    rw [valAt_swapAt_left hi_len hj_len]
    exact hbound hj
  · by_cases hkj : k = j
    · subst k
      rw [valAt_swapAt_right hi_len hj_len]
      exact hbound hi
    · rw [valAt_swapAt_of_ne hi_len hj_len hki hkj]
      exact hbound hk

/-- Fuelled heapify preserves any upper bound on the heap prefix. -/
theorem PrefixLeBound.of_maxHeapifyFuel {fuel : Nat} {a : List Nat}
    {heapSize i bound : Nat}
    (hbound : PrefixLeBound a heapSize bound) (hlen : heapSize ≤ a.length)
    (hi : i < heapSize) :
    PrefixLeBound (maxHeapifyFuel fuel a heapSize i) heapSize bound := by
  intro k hk
  induction fuel generalizing a i k with
  | zero =>
      simpa [maxHeapifyFuel] using hbound hk
  | succ fuel ih =>
      by_cases hmax : maxChildIndex a heapSize i = i
      · simpa [maxHeapifyFuel, hmax] using hbound hk
      · let largest := maxChildIndex a heapSize i
        have hlargest : largest < heapSize := by
          simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
        have hswap_len : heapSize ≤ (swapAt a i largest).length := by
          simpa [largest, swapAt_length] using hlen
        have hswap_bound : PrefixLeBound (swapAt a i largest) heapSize bound :=
          PrefixLeBound.of_swapAt (a := a) (heapSize := heapSize) (bound := bound)
            (i := i) (j := largest) hbound hlen hi hlargest
        have hrec := ih (a := swapAt a i largest) (i := largest) (k := k)
          hswap_bound hswap_len hlargest hk
        simpa [maxHeapifyFuel, hmax, largest] using hrec

/--
After swapping the heap root with the last heap-prefix element and shrinking the
prefix by one, every heap edge except possibly the new root edge is still valid.
-/
theorem ArrayMaxHeapExcept.of_swap_root_last {a : List Nat} {newHeapSize : Nat}
    (hheap : ArrayMaxHeap a (newHeapSize + 1)) :
    ArrayMaxHeapExcept (swapAt a 0 newHeapSize) newHeapSize 0 := by
  have hlen_old : newHeapSize + 1 ≤ a.length := hheap.heapSize_le_length
  have hlen_swapped : newHeapSize ≤ (swapAt a 0 newHeapSize).length := by
    rw [swapAt_length]
    omega
  have h0_len : 0 < a.length := by
    have hpos : 0 < newHeapSize + 1 := by omega
    exact Nat.lt_of_lt_of_le hpos hheap.heapSize_le_length
  have hlast_len : newHeapSize < a.length := by
    omega
  refine ⟨hlen_swapped, ?_, ?_⟩
  · intro i hi hbad hl
    have hi_old : i < newHeapSize + 1 := by omega
    have hl_old : left i < newHeapSize + 1 := by omega
    have hchild_old_len : left i < a.length :=
      Nat.lt_of_lt_of_le hl_old hheap.heapSize_le_length
    have hparent_old_len : i < a.length :=
      Nat.lt_of_lt_of_le hi_old hheap.heapSize_le_length
    have hchild_ne_zero : left i ≠ 0 := by
      unfold left
      omega
    have hchild_ne_last : left i ≠ newHeapSize := by omega
    have hparent_ne_last : i ≠ newHeapSize := by omega
    have hchild_read :
        valAt (swapAt a 0 newHeapSize) (left i) = valAt a (left i) :=
      valAt_swapAt_of_ne h0_len hlast_len hchild_ne_zero hchild_ne_last
    have hparent_read :
        valAt (swapAt a 0 newHeapSize) i = valAt a i :=
      valAt_swapAt_of_ne h0_len hlast_len hbad hparent_ne_last
    have hold := hheap.left_le hi_old hl_old
    rw [← valAt_eq_getElem a hchild_old_len,
      ← valAt_eq_getElem a hparent_old_len] at hold
    have hval :
        valAt (swapAt a 0 newHeapSize) (left i) ≤
          valAt (swapAt a 0 newHeapSize) i := by
      rw [hchild_read, hparent_read]
      exact hold
    rw [valAt_eq_getElem (swapAt a 0 newHeapSize)
        (Nat.lt_of_lt_of_le hl hlen_swapped),
      valAt_eq_getElem (swapAt a 0 newHeapSize)
        (Nat.lt_of_lt_of_le hi hlen_swapped)] at hval
    exact hval
  · intro i hi hbad hr
    have hi_old : i < newHeapSize + 1 := by omega
    have hr_old : right i < newHeapSize + 1 := by omega
    have hchild_old_len : right i < a.length :=
      Nat.lt_of_lt_of_le hr_old hheap.heapSize_le_length
    have hparent_old_len : i < a.length :=
      Nat.lt_of_lt_of_le hi_old hheap.heapSize_le_length
    have hchild_ne_zero : right i ≠ 0 := by
      unfold right
      omega
    have hchild_ne_last : right i ≠ newHeapSize := by omega
    have hparent_ne_last : i ≠ newHeapSize := by omega
    have hchild_read :
        valAt (swapAt a 0 newHeapSize) (right i) = valAt a (right i) :=
      valAt_swapAt_of_ne h0_len hlast_len hchild_ne_zero hchild_ne_last
    have hparent_read :
        valAt (swapAt a 0 newHeapSize) i = valAt a i :=
      valAt_swapAt_of_ne h0_len hlast_len hbad hparent_ne_last
    have hold := hheap.right_le hi_old hr_old
    rw [← valAt_eq_getElem a hchild_old_len,
      ← valAt_eq_getElem a hparent_old_len] at hold
    have hval :
        valAt (swapAt a 0 newHeapSize) (right i) ≤
          valAt (swapAt a 0 newHeapSize) i := by
      rw [hchild_read, hparent_read]
      exact hold
    rw [valAt_eq_getElem (swapAt a 0 newHeapSize)
        (Nat.lt_of_lt_of_le hr hlen_swapped),
      valAt_eq_getElem (swapAt a 0 newHeapSize)
        (Nat.lt_of_lt_of_le hi hlen_swapped)] at hval
    exact hval

/--
After the root/last swap, the sorted suffix grows by one cell.  The new suffix
head contains the old heap root, and the old prefix/suffix boundary says that
this root is at most every element of the old suffix.
-/
theorem SortedSuffix.of_swap_root_last {a : List Nat} {newHeapSize : Nat}
    (hinv : HeapSortLoopInvariant a (newHeapSize + 1)) :
    SortedSuffix (swapAt a 0 newHeapSize) newHeapSize := by
  have hlen_old : newHeapSize + 1 ≤ a.length := hinv.heap.heapSize_le_length
  have h0_len : 0 < a.length := by
    have hpos : 0 < newHeapSize + 1 := by omega
    exact Nat.lt_of_lt_of_le hpos hlen_old
  have hlast_len : newHeapSize < a.length := by omega
  intro p q hp hpq hq
  have hq_old : q < a.length := by
    simpa [swapAt_length] using hq
  by_cases hp_last : p = newHeapSize
  · subst p
    by_cases hq_last : q = newHeapSize
    · subst q
      exact Nat.le_refl _
    · have hq_old_suffix : newHeapSize + 1 ≤ q := by omega
      have hq_ne_zero : q ≠ 0 := by omega
      have hq_read :
          valAt (swapAt a 0 newHeapSize) q = valAt a q :=
        valAt_swapAt_of_ne h0_len hlast_len hq_ne_zero hq_last
      have hhead_read :
          valAt (swapAt a 0 newHeapSize) newHeapSize = valAt a 0 :=
        valAt_swapAt_right h0_len hlast_len
      have hle := hinv.prefix_le_suffix
        (i := 0) (j := q) (by omega) hq_old_suffix hq_old
      rw [hhead_read, hq_read]
      exact hle
  · have hp_old_suffix : newHeapSize + 1 ≤ p := by omega
    have hq_old_suffix : newHeapSize + 1 ≤ q := Nat.le_trans hp_old_suffix hpq
    have hp_ne_zero : p ≠ 0 := by omega
    have hq_ne_zero : q ≠ 0 := by omega
    have hq_ne_last : q ≠ newHeapSize := by omega
    have hp_read :
        valAt (swapAt a 0 newHeapSize) p = valAt a p :=
      valAt_swapAt_of_ne h0_len hlast_len hp_ne_zero hp_last
    have hq_read :
        valAt (swapAt a 0 newHeapSize) q = valAt a q :=
      valAt_swapAt_of_ne h0_len hlast_len hq_ne_zero hq_ne_last
    have hle := hinv.suffix_sorted hp_old_suffix hpq hq_old
    rw [hp_read, hq_read]
    exact hle

/--
After moving the old maximum to the new suffix head, the remaining heap prefix
is still bounded above by that old maximum.
-/
theorem PrefixLeBound.of_swap_root_last {a : List Nat} {newHeapSize : Nat}
    (hinv : HeapSortLoopInvariant a (newHeapSize + 1)) :
    PrefixLeBound (swapAt a 0 newHeapSize) newHeapSize (valAt a 0) := by
  have hlen_old : newHeapSize + 1 ≤ a.length := hinv.heap.heapSize_le_length
  have h0_len : 0 < a.length := by
    have hpos : 0 < newHeapSize + 1 := by omega
    exact Nat.lt_of_lt_of_le hpos hlen_old
  have hlast_len : newHeapSize < a.length := by omega
  intro k hk
  by_cases hk_zero : k = 0
  · subst k
    have hread :
        valAt (swapAt a 0 newHeapSize) 0 = valAt a newHeapSize :=
      valAt_swapAt_left h0_len hlast_len
    rw [hread]
    exact hinv.heap.valAt_le_root (by omega)
  · have hk_last : k ≠ newHeapSize := by omega
    have hread :
        valAt (swapAt a 0 newHeapSize) k = valAt a k :=
      valAt_swapAt_of_ne h0_len hlast_len hk_zero hk_last
    rw [hread]
    exact hinv.heap.valAt_le_root (by omega)

/-- The initial sorted suffix is empty. -/
theorem SortedSuffix.empty (a : List Nat) : SortedSuffix a a.length := by
  intro i j hi _ hj
  omega

/-- With an empty suffix, the prefix/suffix boundary condition is vacuous. -/
theorem PrefixLeSuffix.empty (a : List Nat) : PrefixLeSuffix a a.length := by
  intro i j _ hj hjlen
  omega

/-- Heapifying inside the prefix does not disturb a sorted suffix to its right. -/
theorem SortedSuffix.maxHeapifyFuel {fuel : Nat} {a : List Nat}
    {heapSize i suffixStart : Nat}
    (hlen : heapSize ≤ a.length) (hi : i < heapSize)
    (hboundary : heapSize ≤ suffixStart) (hsuffix : SortedSuffix a suffixStart) :
    SortedSuffix (CLRS.Chapter06.maxHeapifyFuel fuel a heapSize i) suffixStart := by
  intro p q hp hpq hq
  have hq_old : q < a.length := by
    simpa [CLRS.Chapter06.maxHeapifyFuel_length fuel a heapSize i] using hq
  have hp_heap : heapSize ≤ p := Nat.le_trans hboundary hp
  have hq_heap : heapSize ≤ q := Nat.le_trans hp_heap hpq
  have hp_read :
      valAt (CLRS.Chapter06.maxHeapifyFuel fuel a heapSize i) p = valAt a p :=
    maxHeapifyFuel_valAt_of_heapSize_le
      (fuel := fuel) (a := a) (heapSize := heapSize) (i := i) (k := p)
      hlen hi hp_heap
  have hq_read :
      valAt (CLRS.Chapter06.maxHeapifyFuel fuel a heapSize i) q = valAt a q :=
    maxHeapifyFuel_valAt_of_heapSize_le
      (fuel := fuel) (a := a) (heapSize := heapSize) (i := i) (k := q)
      hlen hi hq_heap
  rw [hp_read, hq_read]
  exact hsuffix hp hpq hq_old

/-- A zero-start sorted suffix is the ordinary ascending-order predicate. -/
theorem orderedAsc_of_sortedSuffix_zero {a : List Nat}
    (hsuffix : SortedSuffix a 0) : OrderedAsc a := by
  rw [OrderedAsc, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hval := hsuffix (i := i) (j := j) (Nat.zero_le i) (Nat.le_of_lt hij)
    hj
  simpa [valAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using hval

/-- The heap-built initial array satisfies the CLRS heapsort loop invariant. -/
theorem HeapSortLoopInvariant.initial (xs : List Nat) :
    HeapSortLoopInvariant (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length := by
  refine ⟨arrayBuildMaxHeap_isMaxHeap xs, ?_, ?_⟩
  · exact SortedSuffix.empty (arrayBuildMaxHeap xs)
  · exact PrefixLeSuffix.empty (arrayBuildMaxHeap xs)

/-- At heap size zero, the loop invariant gives the final ascending order. -/
theorem HeapSortLoopInvariant.orderedAsc_of_zero {a : List Nat}
    (h : HeapSortLoopInvariant a 0) : OrderedAsc a :=
  orderedAsc_of_sortedSuffix_zero h.suffix_sorted

/--
When the heap prefix has size at most one, the loop invariant already implies
that the whole array is sorted: either the suffix is the full array, or the
single remaining prefix cell is bounded by every suffix cell.
-/
theorem HeapSortLoopInvariant.orderedAsc_of_heapSize_le_one {a : List Nat}
    {heapSize : Nat} (h : HeapSortLoopInvariant a heapSize)
    (hsmall : heapSize ≤ 1) : OrderedAsc a := by
  rw [OrderedAsc, List.pairwise_iff_getElem]
  intro i j hi hj hij
  by_cases hi_suffix : heapSize ≤ i
  · have hval := h.suffix_sorted hi_suffix (Nat.le_of_lt hij) hj
    simpa [valAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using hval
  · have hi_heap : i < heapSize := Nat.lt_of_not_ge hi_suffix
    have hj_suffix : heapSize ≤ j := by omega
    have hval := h.prefix_le_suffix hi_heap hj_suffix hj
    simpa [valAt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using hval

/--
One CLRS heapsort iteration.  It moves the current maximum to the last cell of
the heap prefix, shrinks the heap prefix, and repairs the new root.
-/
def arrayHeapSortStep (a : List Nat) (heapSize : Nat) : List Nat :=
  match heapSize with
  | 0 => a
  | 1 => a
  | newHeapSize + 2 =>
      let last := newHeapSize + 1
      maxHeapifyFuel (newHeapSize + 1) (swapAt a 0 last) (newHeapSize + 1) 0

/--
One nontrivial CLRS heapsort iteration writes the old heap root into the new
sorted-suffix head.  This is the operational root/last-swap fact behind the
textbook statement that each iteration moves the current maximum into final
position.
-/
theorem arrayHeapSortStep_suffix_head_eq_root {a : List Nat} {newHeapSize : Nat}
    (hinv : HeapSortLoopInvariant a (newHeapSize + 2)) :
    valAt (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) = valAt a 0 := by
  let newSize := newHeapSize + 1
  have hinv' : HeapSortLoopInvariant a (newSize + 1) := by
    simpa [newSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hinv
  have hlen_old : newSize + 1 ≤ a.length := hinv'.heap.heapSize_le_length
  have h0_len : 0 < a.length := by
    have hpos : 0 < newSize + 1 := by omega
    exact Nat.lt_of_lt_of_le hpos hlen_old
  have hlast_len : newSize < a.length := by omega
  have hswapped_len : newSize ≤ (swapAt a 0 newSize).length := by
    rw [swapAt_length]
    omega
  have hpos_new : 0 < newSize := by
    simp [newSize]
  have hheapify_read :
      valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize =
        valAt (swapAt a 0 newSize) newSize :=
    maxHeapifyFuel_valAt_of_heapSize_le
      (fuel := newSize) (a := swapAt a 0 newSize) (heapSize := newSize)
      (i := 0) (k := newSize) hswapped_len hpos_new (Nat.le_refl newSize)
  have hswap_read : valAt (swapAt a 0 newSize) newSize = valAt a 0 :=
    valAt_swapAt_right h0_len hlast_len
  change valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize =
    valAt a 0
  exact hheapify_read.trans hswap_read

/--
One nontrivial CLRS heapsort iteration preserves the full loop invariant: the
heap prefix shrinks by one, the sorted suffix grows by one, and every remaining
prefix element is still bounded by the suffix.
-/
theorem HeapSortLoopInvariant.step {a : List Nat} {newHeapSize : Nat}
    (hinv : HeapSortLoopInvariant a (newHeapSize + 2)) :
    HeapSortLoopInvariant (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) := by
  let newSize := newHeapSize + 1
  have hinv' : HeapSortLoopInvariant a (newSize + 1) := by
    simpa [newSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hinv
  have hlen_old : newSize + 1 ≤ a.length := by
    exact hinv'.heap.heapSize_le_length
  have h0_len : 0 < a.length := by
    have hpos : 0 < newSize + 1 := by omega
    exact Nat.lt_of_lt_of_le hpos hlen_old
  have hlast_len : newSize < a.length := by omega
  have hswapped_len : newSize ≤ (swapAt a 0 newSize).length := by
    rw [swapAt_length]
    omega
  have hpos_new : 0 < newSize := by
    simp [newSize]
  have hexcept :
      ArrayMaxHeapExcept (swapAt a 0 newSize) newSize 0 := by
    exact ArrayMaxHeapExcept.of_swap_root_last
      (a := a) (newHeapSize := newSize) hinv'.heap
  have hheap :
      ArrayMaxHeap (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize :=
    maxHeapifyFuel_root_isMaxHeap hexcept hpos_new (Nat.le_refl newSize)
  have hswap_suffix : SortedSuffix (swapAt a 0 newSize) newSize := by
    exact SortedSuffix.of_swap_root_last (a := a) (newHeapSize := newSize) hinv'
  have hsuffix :
      SortedSuffix (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize :=
    SortedSuffix.maxHeapifyFuel
      (fuel := newSize) (a := swapAt a 0 newSize) (heapSize := newSize)
      (i := 0) (suffixStart := newSize)
      hswapped_len hpos_new (Nat.le_refl newSize) hswap_suffix
  have hswap_bound : PrefixLeBound (swapAt a 0 newSize) newSize (valAt a 0) := by
    exact PrefixLeBound.of_swap_root_last (a := a) (newHeapSize := newSize) hinv'
  have hprefix_bound :
      PrefixLeBound
        (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize (valAt a 0) :=
    PrefixLeBound.of_maxHeapifyFuel
      (fuel := newSize) (a := swapAt a 0 newSize) (heapSize := newSize)
      (i := 0) (bound := valAt a 0) hswap_bound hswapped_len hpos_new
  have hpref :
      PrefixLeSuffix (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize := by
    intro i j hi hj hjlen
    have hstep_len :
        (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0).length = a.length :=
      (maxHeapifyFuel_length newSize (swapAt a 0 newSize) newSize 0).trans
        (swapAt_length a 0 newSize)
    have hj_old : j < a.length := by
      rwa [hstep_len] at hjlen
    have hheapify_read :
        valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) j =
          valAt (swapAt a 0 newSize) j :=
      maxHeapifyFuel_valAt_of_heapSize_le
        (fuel := newSize) (a := swapAt a 0 newSize) (heapSize := newSize)
        (i := 0) (k := j) hswapped_len hpos_new hj
    have hbound_i := hprefix_bound hi
    have hroot_le_suffix :
        valAt a 0 ≤ valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) j := by
      by_cases hj_last : j = newSize
      · subst j
        have hswap_read :
            valAt (swapAt a 0 newSize) newSize = valAt a 0 :=
          valAt_swapAt_right h0_len hlast_len
        rw [hheapify_read, hswap_read]
      · have hj_old_suffix : newSize + 1 ≤ j := by omega
        have hj_ne_zero : j ≠ 0 := by omega
        have hswap_read :
            valAt (swapAt a 0 newSize) j = valAt a j :=
          valAt_swapAt_of_ne h0_len hlast_len hj_ne_zero hj_last
        have hle := hinv.prefix_le_suffix
          (i := 0) (j := j) (by omega) hj_old_suffix hj_old
        rw [hheapify_read, hswap_read]
        exact hle
    exact Nat.le_trans hbound_i hroot_le_suffix
  change
    HeapSortLoopInvariant
      (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize
  exact ⟨hheap, hsuffix, hpref⟩

/--
Fuelled CLRS heapsort loop.  The third argument is the current heap prefix size;
the first argument is only a termination fuel and is instantiated with the input
length by {lit}`arrayHeapSortInPlace`.
-/
def arrayHeapSortInPlaceLoop : Nat → List Nat → Nat → List Nat
  | 0, a, _ => a
  | fuel + 1, a, heapSize =>
      match heapSize with
      | 0 => a
      | 1 => a
      | newHeapSize + 2 =>
          let next := arrayHeapSortStep a (newHeapSize + 2)
          arrayHeapSortInPlaceLoop fuel next (newHeapSize + 1)

/--
If the fuel is at least the current heap size, the repeated CLRS in-place loop
preserves the full loop invariant until the terminal heap prefix has size at
most one.  This is the loop-invariant statement behind the final sortedness
theorem.
-/
theorem arrayHeapSortInPlaceLoop_terminal_invariant (fuel : Nat) {a : List Nat}
    {heapSize : Nat} (hfuel : heapSize ≤ fuel)
    (hinv : HeapSortLoopInvariant a heapSize) :
    ∃ finalHeapSize, finalHeapSize ≤ 1 ∧
      HeapSortLoopInvariant
        (arrayHeapSortInPlaceLoop fuel a heapSize) finalHeapSize := by
  induction fuel generalizing a heapSize with
  | zero =>
      refine ⟨heapSize, ?_, ?_⟩
      · omega
      · simpa [arrayHeapSortInPlaceLoop] using hinv
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          refine ⟨0, ?_, ?_⟩
          · omega
          · simpa [arrayHeapSortInPlaceLoop] using hinv
      | succ heapSize =>
          cases heapSize with
          | zero =>
              refine ⟨1, ?_, ?_⟩
              · omega
              · simpa [arrayHeapSortInPlaceLoop] using hinv
          | succ newHeapSize =>
              have hfuel' : newHeapSize + 1 ≤ fuel := by omega
              have hstep :
                  HeapSortLoopInvariant
                    (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) :=
                HeapSortLoopInvariant.step (a := a) (newHeapSize := newHeapSize) hinv
              simpa [arrayHeapSortInPlaceLoop] using
                ih (a := arrayHeapSortStep a (newHeapSize + 2))
                  (heapSize := newHeapSize + 1) hfuel' hstep

/--
Exact partial-run form of the CLRS shrinking-heap invariant.  Running
{lit}`fuel` genuine loop iterations from a heap prefix of size {lit}`heapSize`
leaves the invariant at precisely {lit}`heapSize - fuel`; the hypothesis rules
out asking the loop to step past the terminal one-cell heap.
-/
theorem arrayHeapSortInPlaceLoop_exact_shrink_invariant (fuel : Nat) {a : List Nat}
    {heapSize : Nat} (hfuel : fuel ≤ heapSize - 1)
    (hinv : HeapSortLoopInvariant a heapSize) :
    HeapSortLoopInvariant
      (arrayHeapSortInPlaceLoop fuel a heapSize) (heapSize - fuel) := by
  induction fuel generalizing a heapSize with
  | zero =>
      simpa [arrayHeapSortInPlaceLoop] using hinv
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          omega
      | succ heapSize =>
          cases heapSize with
          | zero =>
              omega
          | succ newHeapSize =>
              have hfuel' : fuel ≤ (newHeapSize + 1) - 1 := by omega
              have hstep :
                  HeapSortLoopInvariant
                    (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) :=
                HeapSortLoopInvariant.step (a := a) (newHeapSize := newHeapSize) hinv
              have hrec := ih
                (a := arrayHeapSortStep a (newHeapSize + 2))
                (heapSize := newHeapSize + 1) hfuel' hstep
              have hsize : newHeapSize + 2 - (fuel + 1) = newHeapSize + 1 - fuel := by
                omega
              rw [hsize]
              simpa [arrayHeapSortInPlaceLoop] using hrec

/--
Terminal exact-run invariant for the CLRS loop: after exactly
{lit}`heapSize - 1` genuine iterations, the heap prefix is terminal
({lit}`0` for an empty input, otherwise {lit}`1`).
-/
theorem arrayHeapSortInPlaceLoop_exact_terminal_invariant {a : List Nat}
    {heapSize : Nat} (hinv : HeapSortLoopInvariant a heapSize) :
    HeapSortLoopInvariant
      (arrayHeapSortInPlaceLoop (heapSize - 1) a heapSize)
      (heapSize - (heapSize - 1)) := by
  exact arrayHeapSortInPlaceLoop_exact_shrink_invariant
    (fuel := heapSize - 1) (a := a) (heapSize := heapSize) (Nat.le_refl _) hinv

/--
If the fuel is at least the current heap size, the CLRS in-place heapsort loop
finishes in an ascending array.  The proof is the textbook loop-invariant
argument: heap sizes 0 and 1 are terminal, while larger heap sizes use the
single-step invariant theorem and recurse on the smaller heap prefix.
-/
theorem arrayHeapSortInPlaceLoop_orderedAsc (fuel : Nat) {a : List Nat}
    {heapSize : Nat} (hfuel : heapSize ≤ fuel)
    (hinv : HeapSortLoopInvariant a heapSize) :
    OrderedAsc (arrayHeapSortInPlaceLoop fuel a heapSize) := by
  rcases arrayHeapSortInPlaceLoop_terminal_invariant
      (fuel := fuel) (a := a) (heapSize := heapSize) hfuel hinv with
    ⟨finalHeapSize, hsmall, hfinal⟩
  exact hfinal.orderedAsc_of_heapSize_le_one hsmall

/-- In-place heapsort starts by building a max-heap, then runs the CLRS loop. -/
def arrayHeapSortInPlace (xs : List Nat) : List Nat :=
  let heap := arrayBuildMaxHeap xs
  arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length

/-- The top-level CLRS in-place heapsort run terminates with the loop invariant. -/
theorem arrayHeapSortInPlace_terminal_invariant (xs : List Nat) :
    ∃ heapSize, heapSize ≤ 1 ∧
      HeapSortLoopInvariant (arrayHeapSortInPlace xs) heapSize := by
  unfold arrayHeapSortInPlace
  refine ⟨(arrayBuildMaxHeap xs).length - ((arrayBuildMaxHeap xs).length - 1), ?_, ?_⟩
  · omega
  · exact arrayHeapSortInPlaceLoop_exact_terminal_invariant
      (a := arrayBuildMaxHeap xs)
      (heapSize := (arrayBuildMaxHeap xs).length)
      (HeapSortLoopInvariant.initial xs)

/-- One heapsort step preserves list length. -/
theorem arrayHeapSortStep_length (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortStep a heapSize).length = a.length := by
  cases heapSize with
  | zero =>
      simp [arrayHeapSortStep]
  | succ heapSize =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortStep]
      | succ newHeapSize =>
          simp [arrayHeapSortStep]
          exact (maxHeapifyFuel_length (newHeapSize + 1)
            (swapAt a 0 (newHeapSize + 1)) (newHeapSize + 1) 0).trans
            (swapAt_length a 0 (newHeapSize + 1))

/-- One heapsort step preserves the multiset of elements. -/
theorem arrayHeapSortStep_perm (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortStep a heapSize).Perm a := by
  cases heapSize with
  | zero =>
      simp [arrayHeapSortStep]
  | succ heapSize =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortStep]
      | succ newHeapSize =>
          simp [arrayHeapSortStep]
          exact (maxHeapifyFuel_perm (newHeapSize + 1)
            (swapAt a 0 (newHeapSize + 1)) (newHeapSize + 1) 0).trans
            (swapAt_perm a 0 (newHeapSize + 1))

/--
After one nontrivial CLRS heapsort iteration, the newly appended suffix head
dominates every cell still inside the heap prefix.
-/
theorem arrayHeapSortStep_suffix_head_bounds_prefix {a : List Nat}
    {newHeapSize i : Nat} (hinv : HeapSortLoopInvariant a (newHeapSize + 2))
    (hi : i < newHeapSize + 1) :
    valAt (arrayHeapSortStep a (newHeapSize + 2)) i ≤
      valAt (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) := by
  have hstep :
      HeapSortLoopInvariant (arrayHeapSortStep a (newHeapSize + 2))
        (newHeapSize + 1) :=
    HeapSortLoopInvariant.step (a := a) (newHeapSize := newHeapSize) hinv
  have hlast_len : newHeapSize + 1 < (arrayHeapSortStep a (newHeapSize + 2)).length := by
    rw [arrayHeapSortStep_length]
    have hlen : newHeapSize + 2 ≤ a.length := hinv.heap.heapSize_le_length
    omega
  exact hstep.prefix_le_suffix hi (Nat.le_refl (newHeapSize + 1)) hlast_len

/--
Single-step state-correctness package for a nontrivial CLRS heapsort iteration:
the next heap-prefix / sorted-suffix invariant holds, the array elements and
length are preserved, and the old root is exactly the new suffix head.
-/
theorem arrayHeapSortStep_state_correct {a : List Nat} {newHeapSize : Nat}
    (hinv : HeapSortLoopInvariant a (newHeapSize + 2)) :
    HeapSortLoopInvariant (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) ∧
      (arrayHeapSortStep a (newHeapSize + 2)).Perm a ∧
      (arrayHeapSortStep a (newHeapSize + 2)).length = a.length ∧
      valAt (arrayHeapSortStep a (newHeapSize + 2)) (newHeapSize + 1) = valAt a 0 := by
  exact ⟨HeapSortLoopInvariant.step (a := a) (newHeapSize := newHeapSize) hinv,
    arrayHeapSortStep_perm a (newHeapSize + 2),
    arrayHeapSortStep_length a (newHeapSize + 2),
    arrayHeapSortStep_suffix_head_eq_root (a := a) (newHeapSize := newHeapSize) hinv⟩

/-- The in-place heapsort loop preserves list length. -/
theorem arrayHeapSortInPlaceLoop_length (fuel : Nat) (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortInPlaceLoop fuel a heapSize).length = a.length := by
  induction fuel generalizing a heapSize with
  | zero =>
      simp [arrayHeapSortInPlaceLoop]
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortInPlaceLoop]
      | succ heapSize =>
          cases heapSize with
          | zero =>
              simp [arrayHeapSortInPlaceLoop]
          | succ newHeapSize =>
              simp [arrayHeapSortInPlaceLoop]
              exact (ih (arrayHeapSortStep a (newHeapSize + 2))
                (newHeapSize + 1)).trans
                (arrayHeapSortStep_length a (newHeapSize + 2))

/-- The in-place heapsort loop preserves the multiset of elements. -/
theorem arrayHeapSortInPlaceLoop_perm (fuel : Nat) (a : List Nat) (heapSize : Nat) :
    (arrayHeapSortInPlaceLoop fuel a heapSize).Perm a := by
  induction fuel generalizing a heapSize with
  | zero =>
      simp [arrayHeapSortInPlaceLoop]
  | succ fuel ih =>
      cases heapSize with
      | zero =>
          simp [arrayHeapSortInPlaceLoop]
      | succ heapSize =>
          cases heapSize with
          | zero =>
              simp [arrayHeapSortInPlaceLoop]
          | succ newHeapSize =>
              exact (ih (arrayHeapSortStep a (newHeapSize + 2))
                (newHeapSize + 1)).trans
                (arrayHeapSortStep_perm a (newHeapSize + 2))

/--
Exact state-correctness package for a partial CLRS heapsort run.  After
{lit}`fuel` genuine iterations, the heap prefix has size exactly
{lit}`heapSize - fuel`, while the loop has preserved both the input multiset
and the array length.
-/
theorem arrayHeapSortInPlaceLoop_exact_state_correct (fuel : Nat) {a : List Nat}
    {heapSize : Nat} (hfuel : fuel ≤ heapSize - 1)
    (hinv : HeapSortLoopInvariant a heapSize) :
    HeapSortLoopInvariant
        (arrayHeapSortInPlaceLoop fuel a heapSize) (heapSize - fuel) ∧
      (arrayHeapSortInPlaceLoop fuel a heapSize).Perm a ∧
      (arrayHeapSortInPlaceLoop fuel a heapSize).length = a.length := by
  exact ⟨arrayHeapSortInPlaceLoop_exact_shrink_invariant
      (fuel := fuel) (a := a) (heapSize := heapSize) hfuel hinv,
    arrayHeapSortInPlaceLoop_perm fuel a heapSize,
    arrayHeapSortInPlaceLoop_length fuel a heapSize⟩

/--
Reader-facing state-correctness theorem for the fuelled CLRS heapsort loop.
Starting from the full heap-prefix / sorted-suffix invariant and enough fuel,
the loop reaches a terminal heap prefix while preserving sortedness,
permutation, and length.
-/
theorem arrayHeapSortInPlaceLoop_state_correct (fuel : Nat) {a : List Nat}
    {heapSize : Nat} (hfuel : heapSize ≤ fuel)
    (hinv : HeapSortLoopInvariant a heapSize) :
    ∃ finalHeapSize, finalHeapSize ≤ 1 ∧
      HeapSortLoopInvariant
        (arrayHeapSortInPlaceLoop fuel a heapSize) finalHeapSize ∧
      OrderedAsc (arrayHeapSortInPlaceLoop fuel a heapSize) ∧
      (arrayHeapSortInPlaceLoop fuel a heapSize).Perm a ∧
      (arrayHeapSortInPlaceLoop fuel a heapSize).length = a.length := by
  rcases arrayHeapSortInPlaceLoop_terminal_invariant
      (fuel := fuel) (a := a) (heapSize := heapSize) hfuel hinv with
    ⟨finalHeapSize, hsmall, hfinal⟩
  refine ⟨finalHeapSize, hsmall, hfinal, ?_, ?_, ?_⟩
  · exact hfinal.orderedAsc_of_heapSize_le_one hsmall
  · exact arrayHeapSortInPlaceLoop_perm fuel a heapSize
  · exact arrayHeapSortInPlaceLoop_length fuel a heapSize

/-- In-place heapsort preserves list length. -/
theorem arrayHeapSortInPlace_length (xs : List Nat) :
    (arrayHeapSortInPlace xs).length = xs.length := by
  unfold arrayHeapSortInPlace
  exact (arrayHeapSortInPlaceLoop_length ((arrayBuildMaxHeap xs).length - 1)
    (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length).trans
    (by simp [arrayBuildMaxHeap, buildMaxHeapLoop_length])

/-- In-place heapsort preserves the multiset of input elements. -/
theorem arrayHeapSortInPlace_perm (xs : List Nat) :
    (arrayHeapSortInPlace xs).Perm xs := by
  unfold arrayHeapSortInPlace
  exact (arrayHeapSortInPlaceLoop_perm ((arrayBuildMaxHeap xs).length - 1)
    (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length).trans
    (arrayBuildMaxHeap_perm xs)

/-- In-place heapsort returns ascending output. -/
theorem arrayHeapSortInPlace_orderedAsc (xs : List Nat) :
    OrderedAsc (arrayHeapSortInPlace xs) := by
  unfold arrayHeapSortInPlace
  have hinv := arrayHeapSortInPlaceLoop_exact_terminal_invariant
    (a := arrayBuildMaxHeap xs)
    (heapSize := (arrayBuildMaxHeap xs).length)
    (HeapSortLoopInvariant.initial xs)
  exact hinv.orderedAsc_of_heapSize_le_one (by omega)

/--
Reader-facing correctness theorem for the in-place CLRS heapsort refinement:
the shrinking-heap loop returns sorted output, preserves the input multiset, and
keeps the array length unchanged.
-/
theorem arrayHeapSortInPlace_correct (xs : List Nat) :
    OrderedAsc (arrayHeapSortInPlace xs) ∧
      (arrayHeapSortInPlace xs).Perm xs ∧
      (arrayHeapSortInPlace xs).length = xs.length := by
  exact ⟨arrayHeapSortInPlace_orderedAsc xs, arrayHeapSortInPlace_perm xs,
    arrayHeapSortInPlace_length xs⟩

/--
State-correctness theorem for the concrete CLRS in-place heapsort
implementation: the built heap enters the shrinking loop, exits with a terminal
heap prefix, and the final array is sorted, a permutation of the input, and
length-preserving.
-/
theorem arrayHeapSortInPlace_state_correct (xs : List Nat) :
    ∃ heapSize, heapSize ≤ 1 ∧
      HeapSortLoopInvariant (arrayHeapSortInPlace xs) heapSize ∧
      OrderedAsc (arrayHeapSortInPlace xs) ∧
      (arrayHeapSortInPlace xs).Perm xs ∧
      (arrayHeapSortInPlace xs).length = xs.length := by
  unfold arrayHeapSortInPlace
  let heap := arrayBuildMaxHeap xs
  let finalHeapSize := heap.length - (heap.length - 1)
  have hinv :
      HeapSortLoopInvariant
        (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length)
        finalHeapSize := by
    simpa [heap, finalHeapSize] using
      arrayHeapSortInPlaceLoop_exact_terminal_invariant
        (a := heap) (heapSize := heap.length) (HeapSortLoopInvariant.initial xs)
  have hsmall : finalHeapSize ≤ 1 := by
    omega
  have hsorted :
      OrderedAsc (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length) :=
    hinv.orderedAsc_of_heapSize_le_one hsmall
  have hperm :
      (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).Perm heap :=
    arrayHeapSortInPlaceLoop_perm (heap.length - 1) heap heap.length
  have hlen :
      (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).length = heap.length :=
    arrayHeapSortInPlaceLoop_length (heap.length - 1) heap heap.length
  refine ⟨finalHeapSize, hsmall, hinv, hsorted, ?_, ?_⟩
  · exact hperm.trans (by simpa [heap] using arrayBuildMaxHeap_perm xs)
  · exact hlen.trans (by simp [heap, arrayBuildMaxHeap, buildMaxHeapLoop_length])

/--
Exact non-existential state-correctness theorem for the concrete CLRS in-place
heapsort implementation.  It records the terminal heap-prefix size produced by
the exact shrinking loop, then bundles the final invariant, sortedness,
permutation, and length preservation.
-/
theorem arrayHeapSortInPlace_exact_state_correct (xs : List Nat) :
    HeapSortLoopInvariant (arrayHeapSortInPlace xs)
        ((arrayBuildMaxHeap xs).length - ((arrayBuildMaxHeap xs).length - 1)) ∧
      (arrayBuildMaxHeap xs).length - ((arrayBuildMaxHeap xs).length - 1) ≤ 1 ∧
      OrderedAsc (arrayHeapSortInPlace xs) ∧
      (arrayHeapSortInPlace xs).Perm xs ∧
      (arrayHeapSortInPlace xs).length = xs.length := by
  let heap := arrayBuildMaxHeap xs
  have hstate :
      HeapSortLoopInvariant
          (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length)
          (heap.length - (heap.length - 1)) ∧
        (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).Perm heap ∧
        (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).length =
          heap.length :=
    arrayHeapSortInPlaceLoop_exact_state_correct
      (fuel := heap.length - 1) (a := heap) (heapSize := heap.length)
      (Nat.le_refl _) (by simpa [heap] using HeapSortLoopInvariant.initial xs)
  rcases hstate with ⟨hinv, hperm_heap, hlen_heap⟩
  have hsmall : heap.length - (heap.length - 1) ≤ 1 := by
    omega
  have hsorted :
      OrderedAsc (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length) :=
    hinv.orderedAsc_of_heapSize_le_one hsmall
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [arrayHeapSortInPlace, heap] using hinv
  · simpa [heap] using hsmall
  · simpa [arrayHeapSortInPlace, heap] using hsorted
  · have hperm : (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).Perm xs :=
      hperm_heap.trans (by simpa [heap] using arrayBuildMaxHeap_perm xs)
    simpa [arrayHeapSortInPlace, heap] using hperm
  · have hlen :
        (arrayHeapSortInPlaceLoop (heap.length - 1) heap heap.length).length =
          xs.length :=
      hlen_heap.trans
        (by simp [heap, arrayBuildMaxHeap, buildMaxHeapLoop_length])
    simpa [arrayHeapSortInPlace, heap] using hlen

/-! ## Array-level heapsort refinement theorems -/

/-- Array-facing name for the CLRS in-place heapsort implementation. -/
def arrayHeapSort (xs : List Nat) : List Nat :=
  arrayHeapSortInPlace xs

/-- The public array-facing heapsort interface is the in-place CLRS loop. -/
theorem arrayHeapSort_eq_arrayHeapSortInPlace (xs : List Nat) :
    arrayHeapSort xs = arrayHeapSortInPlace xs := by
  rfl

/-- Public heapsort also exposes the terminal loop invariant of the in-place run. -/
theorem arrayHeapSort_terminal_invariant (xs : List Nat) :
    ∃ heapSize, heapSize ≤ 1 ∧
      HeapSortLoopInvariant (arrayHeapSort xs) heapSize := by
  simpa [arrayHeapSort] using arrayHeapSortInPlace_terminal_invariant xs

/--
Public state-correctness theorem for Chapter 6 heapsort.  This is the compact
CLRS loop-invariant specification exposed by the array-facing interface.
-/
theorem arrayHeapSort_state_correct (xs : List Nat) :
    ∃ heapSize, heapSize ≤ 1 ∧
      HeapSortLoopInvariant (arrayHeapSort xs) heapSize ∧
      OrderedAsc (arrayHeapSort xs) ∧
      (arrayHeapSort xs).Perm xs ∧
      (arrayHeapSort xs).length = xs.length := by
  simpa [arrayHeapSort] using arrayHeapSortInPlace_state_correct xs

/-- Public non-existential exact state package for Chapter 6 heapsort. -/
theorem arrayHeapSort_exact_state_correct (xs : List Nat) :
    HeapSortLoopInvariant (arrayHeapSort xs)
        ((arrayBuildMaxHeap xs).length - ((arrayBuildMaxHeap xs).length - 1)) ∧
      (arrayBuildMaxHeap xs).length - ((arrayBuildMaxHeap xs).length - 1) ≤ 1 ∧
      OrderedAsc (arrayHeapSort xs) ∧
      (arrayHeapSort xs).Perm xs ∧
      (arrayHeapSort xs).length = xs.length := by
  simpa [arrayHeapSort] using arrayHeapSortInPlace_exact_state_correct xs

/-- Array-facing heapsort returns ascending output. -/
theorem arrayHeapSort_orderedAsc (xs : List Nat) :
    OrderedAsc (arrayHeapSort xs) := by
  simpa [arrayHeapSort] using arrayHeapSortInPlace_orderedAsc xs

/-- Array-facing heapsort preserves the input elements. -/
theorem arrayHeapSort_perm (xs : List Nat) :
    (arrayHeapSort xs).Perm xs := by
  simpa [arrayHeapSort] using arrayHeapSortInPlace_perm xs

/--
Main Chapter 6 heapsort specification.  The public {lit}`arrayHeapSort`
interface is the in-place CLRS loop, and it returns a sorted permutation of the
input with the same length.
-/
theorem arrayHeapSort_correct (xs : List Nat) :
    OrderedAsc (arrayHeapSort xs) ∧
      (arrayHeapSort xs).Perm xs ∧
      (arrayHeapSort xs).length = xs.length := by
  exact ⟨arrayHeapSort_orderedAsc xs, arrayHeapSort_perm xs,
    by simpa [arrayHeapSort] using arrayHeapSortInPlace_length xs⟩

end Chapter06
end CLRS
