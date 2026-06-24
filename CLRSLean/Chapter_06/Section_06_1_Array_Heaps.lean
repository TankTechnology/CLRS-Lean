import CLRSLean.Chapter_06.Section_06_1_Heapsort

/-!
# CLRS Chapter 6.1-6.4 - Array Heap Layer

This file strengthens the first Chapter 6 pass with an array-indexed heap
interface.  Lists play the role of arrays, while CLRS parent/child indices are
the ordinary zero-based formulas:

- left child: `2 * i + 1`;
- right child: `2 * i + 2`;
- parent: `(i - 1) / 2`.

Main results:

- Theorem {lit}`orderedDesc_arrayMaxHeap`: a descending list satisfies the
  indexed max-heap predicate.
- Theorem {lit}`arrayBuildMaxHeap_isMaxHeap`: the existing functional
  `buildMaxHeap` refines the indexed heap predicate.
- Theorem {lit}`swapAt_perm`: the array swap operation preserves the multiset of
  elements.
- Theorems {lit}`valAt_swapAt_left` and {lit}`valAt_swapAt_right`: after a valid
  swap, the two exchanged cells contain each other's old values.
- Theorem {lit}`maxHeapifyFuel_perm`: the executable, fuelled
  `maxHeapifyFuel` loop preserves the multiset of elements.
- Theorems {lit}`valAt_i_le_maxChildIndex`,
  {lit}`valAt_left_le_maxChildIndex`, and
  {lit}`valAt_right_le_maxChildIndex`: the CLRS `largest` choice is locally
  maximal among the root and in-heap children.
- Theorem {lit}`maxChildIndex_eq_self_left_le` and
  {lit}`maxChildIndex_eq_self_right_le`: the no-swap branch of `MAX-HEAPIFY`
  has exactly the expected local heap inequalities.
- Theorem {lit}`arrayMaxHeap_of_except_of_maxChildIndex_self`: if all heap
  inequalities except possibly those at `i` already hold and `MAX-HEAPIFY`
  does not swap at `i`, the whole prefix is an indexed max-heap.
- Theorem {lit}`ArrayMaxHeap.getElem_le_root`: every element in an indexed
  max-heap prefix is bounded by the root.

Current gaps:

- The full recursive repair theorem for `maxHeapifyFuel` is still the remaining
  hard step: after swapping with the larger child, prove the child subtree is
  repaired recursively.  This file provides the array predicate, swap
  permutation, and no-swap branch needed for that proof.
- Runtime bounds and a full RAM semantics remain outside this mathematical
  array layer.
-/

namespace CLRS
namespace Chapter06

/-! ## CLRS array indices and heap predicate -/

/-- Zero-based left-child index. -/
def left (i : Nat) : Nat :=
  2 * i + 1

/-- Zero-based right-child index. -/
def right (i : Nat) : Nat :=
  2 * i + 2

/-- Zero-based parent index, with `parent 0 = 0` by natural subtraction. -/
def parent (i : Nat) : Nat :=
  (i - 1) / 2

/-- Every positive zero-based heap index has a strictly smaller parent. -/
theorem parent_lt_self {i : Nat} (hi : 0 < i) : parent i < i := by
  unfold parent
  omega

/-- Every positive index is either the left or right child of its parent. -/
theorem eq_left_or_right_parent {i : Nat} (hi : 0 < i) :
    i = left (parent i) ∨ i = right (parent i) := by
  unfold parent left right
  omega

/--
Indexed max-heap predicate over the prefix `0 ..< heapSize` of a list-backed
array.  Every in-heap parent is at least each in-heap child.
-/
structure ArrayMaxHeap (a : List Nat) (heapSize : Nat) : Prop where
  heapSize_le_length : heapSize ≤ a.length
  left_le : ∀ {i : Nat}, (hi : i < heapSize) → (hl : left i < heapSize) →
    a[left i]'(Nat.lt_of_lt_of_le hl heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)
  right_le : ∀ {i : Nat}, (hi : i < heapSize) → (hr : right i < heapSize) →
    a[right i]'(Nat.lt_of_lt_of_le hr heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)

/--
The same heap predicate with one possible bad parent.  This is the CLRS
precondition for `MAX-HEAPIFY`: both child subtrees are already heaps, so every
edge except the two outgoing edges from the root under repair is valid.
-/
structure ArrayMaxHeapExcept (a : List Nat) (heapSize bad : Nat) : Prop where
  heapSize_le_length : heapSize ≤ a.length
  left_le : ∀ {i : Nat}, (hi : i < heapSize) → i ≠ bad →
    (hl : left i < heapSize) →
    a[left i]'(Nat.lt_of_lt_of_le hl heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)
  right_le : ∀ {i : Nat}, (hi : i < heapSize) → i ≠ bad →
    (hr : right i < heapSize) →
    a[right i]'(Nat.lt_of_lt_of_le hr heapSize_le_length) ≤
    a[i]'(Nat.lt_of_lt_of_le hi heapSize_le_length)

/-- A heap remains a heap after forgetting the obligations at one parent. -/
theorem ArrayMaxHeap.except {a : List Nat} {heapSize bad : Nat}
    (h : ArrayMaxHeap a heapSize) : ArrayMaxHeapExcept a heapSize bad := by
  refine ⟨h.heapSize_le_length, ?_, ?_⟩
  · intro i hi _ hl
    exact h.left_le hi hl
  · intro i hi _ hr
    exact h.right_le hi hr

/--
In an indexed max-heap, the root bounds every element in the heap prefix.  This
is the array-level proof behind CLRS `HEAP-MAXIMUM`.
-/
theorem ArrayMaxHeap.getElem_le_root {a : List Nat} {heapSize : Nat}
    (h : ArrayMaxHeap a heapSize) {i : Nat} (hi : i < heapSize) :
    a[i]'(Nat.lt_of_lt_of_le hi h.heapSize_le_length) ≤
      a[0]'(Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) h.heapSize_le_length) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      cases i with
      | zero =>
          simp
      | succ k =>
          let p := parent (Nat.succ k)
          have hpos : 0 < Nat.succ k := Nat.succ_pos k
          have hplt : p < Nat.succ k := parent_lt_self hpos
          have hpheap : p < heapSize := Nat.lt_trans hplt hi
          have hedge :
              a[Nat.succ k]'(Nat.lt_of_lt_of_le hi h.heapSize_le_length) ≤
                a[p]'(Nat.lt_of_lt_of_le hpheap h.heapSize_le_length) := by
            rcases eq_left_or_right_parent hpos with hleft | hright
            · have hchildEq : left p = Nat.succ k := hleft.symm
              have hchild : left p < heapSize := by simpa [hchildEq] using hi
              have hle := h.left_le hpheap hchild
              simpa [p, hchildEq] using hle
            · have hchildEq : right p = Nat.succ k := hright.symm
              have hchild : right p < heapSize := by simpa [hchildEq] using hi
              have hle := h.right_le hpheap hchild
              simpa [p, hchildEq] using hle
          have hparent := ih p hplt hpheap
          exact Nat.le_trans hedge (by simpa using hparent)

/--
In a descending list, a smaller index contains a value at least as large as any
larger index.  This bridges the first functional heap model to the indexed heap
predicate used by the CLRS array layer.
-/
theorem orderedDesc_getElem_le {xs : List Nat} (hxs : OrderedDesc xs)
    {i j : Nat} (hij : i < j) (hj : j < xs.length) : xs[j] ≤ xs[i] := by
  induction xs generalizing i j with
  | nil =>
      simp at hj
  | cons x xs ih =>
      cases j with
      | zero =>
          omega
      | succ j =>
          cases i with
          | zero =>
              have hj' : j < xs.length := by simpa using hj
              have htailmem : xs[j] ∈ xs := List.getElem_mem hj'
              have hx := (List.pairwise_cons.mp hxs).1 (xs[j]'hj') htailmem
              simpa using hx
          | succ i =>
              have htail : OrderedDesc xs := (List.pairwise_cons.mp hxs).2
              have hij' : i < j := by omega
              have hj' : j < xs.length := by simpa using hj
              simpa using ih htail hij' hj'

/-- A descending list is an indexed max-heap on any prefix. -/
theorem orderedDesc_arrayMaxHeap {a : List Nat} {heapSize : Nat}
    (hlen : heapSize ≤ a.length) (h : OrderedDesc a) :
    ArrayMaxHeap a heapSize := by
  refine ⟨hlen, ?_, ?_⟩
  · intro i hi hl
    exact orderedDesc_getElem_le h (by simp [left]; omega)
      (Nat.lt_of_lt_of_le hl hlen)
  · intro i hi hr
    exact orderedDesc_getElem_le h (by simp [right]; omega)
      (Nat.lt_of_lt_of_le hr hlen)

/-! ## Swaps and fuelled `MAX-HEAPIFY` -/

/-- Read an array cell with fallback zero outside the list. -/
def valAt (a : List Nat) (i : Nat) : Nat :=
  a.getD i 0

/-- Inside bounds, `valAt` is the ordinary list-backed array read. -/
theorem valAt_eq_getElem (a : List Nat) {i : Nat} (hi : i < a.length) :
    valAt a i = a[i] := by
  simp [valAt, List.getElem?_eq_getElem hi]

/-- Swap two array cells when both indices are in bounds; otherwise leave the list unchanged. -/
def swapAt (a : List Nat) (i j : Nat) : List Nat :=
  match a[i]?, a[j]? with
  | some ai, some aj => (a.set i aj).set j ai
  | _, _ => a

/-- Auxiliary permutation lemma for swapping the head with a later cell. -/
theorem cons_set_perm_of_get? {xs : List Nat} {j x y : Nat}
    (h : xs[j]? = some y) : (y :: xs.set j x).Perm (x :: xs) := by
  induction xs generalizing j with
  | nil =>
      simp at h
  | cons z zs ih =>
      cases j with
      | zero =>
          simp at h
          subst y
          simp [List.set]
          exact List.Perm.swap x z zs
      | succ j =>
          simp at h
          have ih' := ih h
          simp [List.set]
          exact ((List.Perm.swap y z (zs.set j x)).symm.trans
            (List.Perm.cons z ih')).trans (List.Perm.swap z x zs).symm

/-- Swapping two cells preserves list length. -/
theorem swapAt_length (a : List Nat) (i j : Nat) :
    (swapAt a i j).length = a.length := by
  unfold swapAt
  cases a[i]? <;> cases a[j]? <;> simp

/-- Swapping two cells preserves the multiset of elements. -/
theorem swapAt_perm (a : List Nat) (i j : Nat) :
    (swapAt a i j).Perm a := by
  induction a generalizing i j with
  | nil =>
      simp [swapAt]
  | cons x xs ih =>
      cases i with
      | zero =>
          cases j with
          | zero =>
              simp [swapAt]
          | succ j =>
              unfold swapAt
              simp
              cases h : xs[j]? with
              | none =>
                  simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get? (xs := xs) (j := j) (x := x) h
      | succ i =>
          cases j with
          | zero =>
              unfold swapAt
              simp
              cases h : xs[i]? with
              | none =>
                  simp
              | some y =>
                  simpa [h, List.set] using
                    cons_set_perm_of_get? (xs := xs) (j := i) (x := x) h
          | succ j =>
              cases hi : xs[i]? with
              | none =>
                  simp [swapAt, hi]
              | some ai =>
                  cases hj : xs[j]? with
                  | none =>
                      simp [swapAt, hi, hj]
                  | some aj =>
                      simpa [swapAt, hi, hj, List.set] using ih i j

/-- After an in-bounds swap, the first index contains the old value at the second. -/
theorem valAt_swapAt_left {a : List Nat} {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) :
    valAt (swapAt a i j) i = valAt a j := by
  by_cases hij : i = j
  · subst j
    simp [swapAt, valAt, List.getElem?_eq_getElem hi]
  · unfold swapAt
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp [valAt, Ne.symm hij]
    rw [List.getElem?_set_self']
    simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]

/-- After an in-bounds swap, the second index contains the old value at the first. -/
theorem valAt_swapAt_right {a : List Nat} {i j : Nat}
    (hi : i < a.length) (hj : j < a.length) :
    valAt (swapAt a i j) j = valAt a i := by
  by_cases hij : i = j
  · subst j
    simp [swapAt, valAt, List.getElem?_eq_getElem hi]
  · unfold swapAt
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
    simp [valAt]
    rw [List.getElem?_set_self']
    have hjset : j < (a.set i a[j]).length := by
      simpa [List.length_set] using hj
    simp [List.getElem?_eq_getElem hjset, List.getElem?_eq_getElem hi]

/-- Choose between a current largest index and a candidate child. -/
def largerIndex (a : List Nat) (heapSize current candidate : Nat) : Nat :=
  if candidate < heapSize then
    if valAt a current < valAt a candidate then candidate else current
  else
    current

/-- The CLRS choice of the largest among `i`, `left i`, and `right i`. -/
def maxChildIndex (a : List Nat) (heapSize i : Nat) : Nat :=
  largerIndex a heapSize (largerIndex a heapSize i (left i)) (right i)

/-- A `largerIndex` result is at least the current index's key. -/
theorem valAt_current_le_largerIndex (a : List Nat)
    (heapSize current candidate : Nat) :
    valAt a current ≤ valAt a (largerIndex a heapSize current candidate) := by
  unfold largerIndex
  by_cases hc : candidate < heapSize
  · simp [hc]
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt]
      exact Nat.le_of_lt hlt
    · simp [hlt]
  · simp [hc]

/-- If the candidate is in the heap, a `largerIndex` result is at least it. -/
theorem valAt_candidate_le_largerIndex {a : List Nat}
    {heapSize current candidate : Nat} (hcandidate : candidate < heapSize) :
    valAt a candidate ≤ valAt a (largerIndex a heapSize current candidate) := by
  unfold largerIndex
  simp [hcandidate]
  by_cases hlt : valAt a current < valAt a candidate
  · simp [hlt]
  · simp [hlt]
    exact Nat.le_of_not_gt hlt

/-- If the current index is inside the heap, the selected larger index is too. -/
theorem largerIndex_lt_heapSize {a : List Nat}
    {heapSize current candidate : Nat} (hcurrent : current < heapSize) :
    largerIndex a heapSize current candidate < heapSize := by
  unfold largerIndex
  by_cases hc : candidate < heapSize
  · simp [hc]
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt, hc]
    · simp [hlt, hcurrent]
  · simp [hc, hcurrent]

/-- If the root is inside the heap, the CLRS `largest` index is inside too. -/
theorem maxChildIndex_lt_heapSize {a : List Nat} {heapSize i : Nat}
    (hi : i < heapSize) : maxChildIndex a heapSize i < heapSize := by
  unfold maxChildIndex
  exact largerIndex_lt_heapSize (largerIndex_lt_heapSize hi)

/-- The selected CLRS `largest` key is at least the original root key. -/
theorem valAt_i_le_maxChildIndex (a : List Nat) (heapSize i : Nat) :
    valAt a i ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_current_le_largerIndex a heapSize i (left i))
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS `largest` key is at least the left child's key. -/
theorem valAt_left_le_maxChildIndex {a : List Nat} {heapSize i : Nat}
    (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_candidate_le_largerIndex (a := a) (current := i) hl)
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS `largest` key is at least the right child's key. -/
theorem valAt_right_le_maxChildIndex {a : List Nat} {heapSize i : Nat}
    (hr : right i < heapSize) :
    valAt a (right i) ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact valAt_candidate_le_largerIndex (a := a)
    (current := largerIndex a heapSize i (left i)) hr

/-- A left child index is strictly different from its parent index. -/
theorem left_ne_self (i : Nat) : left i ≠ i := by
  unfold left
  omega

/-- A right child index is strictly different from its parent index. -/
theorem right_ne_self (i : Nat) : right i ≠ i := by
  unfold right
  omega

/--
Fuelled executable version of `MAX-HEAPIFY`.  Each recursive call swaps the
current root with its largest in-heap child and continues at that child.
-/
def maxHeapifyFuel : Nat → List Nat → Nat → Nat → List Nat
  | 0, a, _, _ => a
  | fuel + 1, a, heapSize, i =>
      let largest := maxChildIndex a heapSize i
      if largest = i then
        a
      else
        maxHeapifyFuel fuel (swapAt a i largest) heapSize largest

/-- Fuelled heapify preserves list length. -/
theorem maxHeapifyFuel_length (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (maxHeapifyFuel fuel a heapSize i).length = a.length := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuel]
  | succ fuel ih =>
      simp [maxHeapifyFuel]
      split
      · rfl
      · trans (swapAt a i (maxChildIndex a heapSize i)).length
        · exact ih (swapAt a i (maxChildIndex a heapSize i))
            (maxChildIndex a heapSize i)
        · exact swapAt_length a i (maxChildIndex a heapSize i)

/-- Fuelled heapify preserves the multiset of elements. -/
theorem maxHeapifyFuel_perm (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (maxHeapifyFuel fuel a heapSize i).Perm a := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuel]
  | succ fuel ih =>
      simp [maxHeapifyFuel]
      split
      · rfl
      · exact (ih (swapAt a i (maxChildIndex a heapSize i))
          (maxChildIndex a heapSize i)).trans
          (swapAt_perm a i (maxChildIndex a heapSize i))

/--
If a `largerIndex` call returns a target different from its candidate, then the
target must have been the current index.  CLRS uses the same case split when
reasoning about the variable `largest`.
-/
theorem largerIndex_eq_target_forces_current {a : List Nat}
    {heapSize current candidate target : Nat}
    (h : largerIndex a heapSize current candidate = target)
    (hcandidate : candidate ≠ target) : current = target := by
  unfold largerIndex at h
  by_cases hin : candidate < heapSize
  · simp [hin] at h
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt] at h
      exact False.elim (hcandidate h)
    · simpa [hlt] using h
  · simpa [hin] using h

/--
If `largerIndex` keeps the current index and the candidate is in the heap, then
the candidate's key is no larger than the current key.
-/
theorem largerIndex_eq_current_le {a : List Nat}
    {heapSize current candidate : Nat}
    (h : largerIndex a heapSize current candidate = current)
    (hcandidate : candidate < heapSize) :
    valAt a candidate ≤ valAt a current := by
  unfold largerIndex at h
  simp [hcandidate] at h
  by_cases hlt : valAt a current < valAt a candidate
  · simp [hlt] at h
    subst candidate
    exact Nat.le_refl _
  · exact Nat.le_of_not_gt hlt

/--
If `MAX-HEAPIFY` chooses not to swap, the left-child inequality at `i` holds.
-/
theorem maxChildIndex_eq_self_left_le {a : List Nat} {heapSize i : Nat}
    (hmax : maxChildIndex a heapSize i = i) (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a i := by
  have hleft : largerIndex a heapSize i (left i) = i :=
    largerIndex_eq_target_forces_current
      (by simpa [maxChildIndex] using hmax) (right_ne_self i)
  exact largerIndex_eq_current_le hleft hl

/--
If `MAX-HEAPIFY` chooses not to swap, the right-child inequality at `i` holds.
-/
theorem maxChildIndex_eq_self_right_le {a : List Nat} {heapSize i : Nat}
    (hmax : maxChildIndex a heapSize i = i) (hr : right i < heapSize) :
    valAt a (right i) ≤ valAt a i := by
  have hleft : largerIndex a heapSize i (left i) = i :=
    largerIndex_eq_target_forces_current
      (by simpa [maxChildIndex] using hmax) (right_ne_self i)
  have hright : largerIndex a heapSize i (right i) = i := by
    simpa [maxChildIndex, hleft] using hmax
  exact largerIndex_eq_current_le hright hr

/--
No-swap correctness for `MAX-HEAPIFY`: if all heap edges except those outgoing
from `i` are already valid, and `MAX-HEAPIFY` leaves `i` in place, the entire
prefix is a max-heap.
-/
theorem arrayMaxHeap_of_except_of_maxChildIndex_self {a : List Nat}
    {heapSize i : Nat} (hexcept : ArrayMaxHeapExcept a heapSize i)
    (hmax : maxChildIndex a heapSize i = i) : ArrayMaxHeap a heapSize := by
  refine ⟨hexcept.heapSize_le_length, ?_, ?_⟩
  · intro j hj hl
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_left_le hmax hl
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.left_le hj hji hl
  · intro j hj hr
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_right_le hmax hr
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.right_le hj hji hr

/-! ## Array-level build and heapsort refinement theorems -/

/-- Array-facing name for the current heap builder. -/
def arrayBuildMaxHeap (xs : List Nat) : List Nat :=
  buildMaxHeap xs

/-- The array-facing heap builder returns an indexed max-heap. -/
theorem arrayBuildMaxHeap_isMaxHeap (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length := by
  exact orderedDesc_arrayMaxHeap (Nat.le_refl _)
    (by simpa [arrayBuildMaxHeap] using buildMaxHeap_orderedDesc xs)

/-- The array-facing heap builder preserves the input elements. -/
theorem arrayBuildMaxHeap_perm (xs : List Nat) :
    (arrayBuildMaxHeap xs).Perm xs := by
  simpa [arrayBuildMaxHeap] using buildMaxHeap_perm xs

/-- Array-facing name for the current heapsort implementation. -/
def arrayHeapSort (xs : List Nat) : List Nat :=
  heapSort xs

/-- Array-facing heapsort returns ascending output. -/
theorem arrayHeapSort_orderedAsc (xs : List Nat) :
    OrderedAsc (arrayHeapSort xs) := by
  simpa [arrayHeapSort] using heapSort_orderedAsc xs

/-- Array-facing heapsort preserves the input elements. -/
theorem arrayHeapSort_perm (xs : List Nat) :
    (arrayHeapSort xs).Perm xs := by
  simpa [arrayHeapSort] using heapSort_perm xs

end Chapter06
end CLRS
