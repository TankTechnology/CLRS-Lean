import CLRSLean.FourthEdition.Chapter_06.Section_06_2_Maintaining_Heap_Property

/-!
# CLRS Section 6.3 - Building a Heap

This section proves the indexed version of CLRS {lit}`BUILD-MAX-HEAP`.  The
main builder starts from the last internal-node layer and repeatedly calls the
fuelled {lit}`MAX-HEAPIFY` theorem from Section 6.2.

Main results:

- Theorem {lit}`ArrayMaxHeapFrom.of_half`: every node from {lit}`heapSize / 2`
  onward is a leaf, so that suffix is already a localized max-heap.
- Theorem {lit}`buildMaxHeapLoop_isMaxHeap`: the bottom-up repeated
  {lit}`MAX-HEAPIFY` loop returns a global indexed max-heap.
- Theorem {lit}`buildMaxHeapLoop_perm`: the bottom-up loop preserves the input
  multiset.
- Theorem {lit}`arrayBuildMaxHeap_isMaxHeap`: the array-facing builder returns
  an indexed max-heap over the whole list.
- Theorem {lit}`arrayBuildMaxHeap_perm`: the builder preserves the multiset of
  input elements.
- Theorem {lit}`arrayBuildMaxHeap_correct`: the reader-facing correctness
  theorem bundling heapness, permutation, and length preservation.

Remaining refinements:

- This section proves the CLRS-style bottom-up heap construction used by the
  in-place heapsort loop.  Later work can connect it to a shared imperative
  array semantics and cost model.
-/

namespace CLRS
namespace Chapter06

/-! ## Bottom-up heap construction -/

/-- Array-facing name for the older compact functional heap builder. -/
def arrayBuildMaxHeapFunctional (xs : List Nat) : List Nat :=
  buildMaxHeap xs

/--
Bottom-up heap construction loop.  With count {lit}`k + 1`, it first heapifies
index {lit}`k`, then continues with {lit}`k - 1`, and so on down to zero.
-/
def buildMaxHeapLoop : Nat → List Nat → Nat → List Nat
  | 0, a, _ => a
  | count + 1, a, heapSize =>
      buildMaxHeapLoop count (maxHeapifyFuel heapSize a heapSize count) heapSize

/-- The bottom-up build loop preserves list length. -/
theorem buildMaxHeapLoop_length (count : Nat) (a : List Nat) (heapSize : Nat) :
    (buildMaxHeapLoop count a heapSize).length = a.length := by
  induction count generalizing a with
  | zero =>
      simp [buildMaxHeapLoop]
  | succ count ih =>
      simp [buildMaxHeapLoop]
      exact (ih (maxHeapifyFuel heapSize a heapSize count)).trans
        (maxHeapifyFuel_length heapSize a heapSize count)

/-- The bottom-up build loop preserves the multiset of elements. -/
theorem buildMaxHeapLoop_perm (count : Nat) (a : List Nat) (heapSize : Nat) :
    (buildMaxHeapLoop count a heapSize).Perm a := by
  induction count generalizing a with
  | zero =>
      simp [buildMaxHeapLoop]
  | succ count ih =>
      exact (ih (maxHeapifyFuel heapSize a heapSize count)).trans
        (maxHeapifyFuel_perm heapSize a heapSize count)

/--
Every parent index from {lit}`heapSize / 2` onward is a leaf.  This is the
zero-based version of the CLRS observation that nodes after
{lit}`⌊heap-size / 2⌋` are leaves.
-/
theorem ArrayMaxHeapFrom.of_half {a : List Nat} {heapSize : Nat}
    (hlen : heapSize ≤ a.length) :
    ArrayMaxHeapFrom a heapSize (heapSize / 2) := by
  refine ⟨hlen, ?_, ?_⟩
  · intro i hhalf _ hl
    exfalso
    unfold left at hl
    omega
  · intro i hhalf _ hr
    exfalso
    unfold right at hr
    omega

/--
If all localized heap obligations after {lit}`i` hold, then the same localized
region starting at {lit}`i` has at most one bad parent, namely {lit}`i` itself.
-/
theorem ArrayMaxHeapFrom.except_pred {a : List Nat} {heapSize i : Nat}
    (h : ArrayMaxHeapFrom a heapSize (i + 1)) :
    ArrayMaxHeapExceptFrom a heapSize i i := by
  refine ⟨h.heapSize_le_length, ?_, ?_⟩
  · intro j hij hj hji hl
    have hnext : i + 1 ≤ j := by omega
    exact h.left_le hnext hj hl
  · intro j hij hj hji hr
    have hnext : i + 1 ≤ j := by omega
    exact h.right_le hnext hj hr

/--
Correctness of the bottom-up build loop.  If the suffix of parent obligations
from {lit}`count` onward is already a localized heap, heapifying
{lit}`count - 1, ..., 0` produces a global max-heap.
-/
theorem buildMaxHeapLoop_isMaxHeap {count : Nat} {a : List Nat} {heapSize : Nat}
    (hfrom : ArrayMaxHeapFrom a heapSize count) (hcount : count ≤ heapSize) :
    ArrayMaxHeap (buildMaxHeapLoop count a heapSize) heapSize := by
  induction count generalizing a with
  | zero =>
      simpa [buildMaxHeapLoop] using ArrayMaxHeapFrom.to_global hfrom
  | succ count ih =>
      have hi : count < heapSize := by omega
      have hrepair :
          ArrayMaxHeapFrom
            (maxHeapifyFuel heapSize a heapSize count) heapSize count :=
        maxHeapifyFuel_repair_subtree
          (ArrayMaxHeapFrom.except_pred hfrom) hi (by omega)
      simpa [buildMaxHeapLoop] using ih hrepair (by omega)

/-- CLRS-style array build: heapify all internal nodes from right to left. -/
def arrayBuildMaxHeap (xs : List Nat) : List Nat :=
  buildMaxHeapLoop (xs.length / 2) xs xs.length

/-! ## Array-level build refinement theorems -/

/-- The older compact functional heap builder returns an indexed max-heap. -/
theorem arrayBuildMaxHeapFunctional_isMaxHeap (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeapFunctional xs)
      (arrayBuildMaxHeapFunctional xs).length := by
  exact orderedDesc_arrayMaxHeap (Nat.le_refl _)
    (by simpa [arrayBuildMaxHeapFunctional] using buildMaxHeap_orderedDesc xs)

/-- The older compact functional heap builder preserves the input elements. -/
theorem arrayBuildMaxHeapFunctional_perm (xs : List Nat) :
    (arrayBuildMaxHeapFunctional xs).Perm xs := by
  simpa [arrayBuildMaxHeapFunctional] using buildMaxHeap_perm xs

/-- The array-facing heap builder returns an indexed max-heap. -/
theorem arrayBuildMaxHeap_isMaxHeap (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length := by
  have hheap :
      ArrayMaxHeap (arrayBuildMaxHeap xs) xs.length := by
    simpa [arrayBuildMaxHeap] using
      buildMaxHeapLoop_isMaxHeap
        (ArrayMaxHeapFrom.of_half (a := xs) (heapSize := xs.length) (Nat.le_refl _))
        (Nat.div_le_self xs.length 2)
  simpa [arrayBuildMaxHeap, buildMaxHeapLoop_length] using hheap

/--
Named repeated-heapify form of the array-facing build theorem, useful for status
pages and later Section 6.4 refinements.
-/
theorem arrayBuildMaxHeapRepeated_isMaxHeap (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length :=
  arrayBuildMaxHeap_isMaxHeap xs

/-- The array-facing heap builder preserves the input elements. -/
theorem arrayBuildMaxHeap_perm (xs : List Nat) :
    (arrayBuildMaxHeap xs).Perm xs := by
  simpa [arrayBuildMaxHeap] using
    buildMaxHeapLoop_perm (xs.length / 2) xs xs.length

/--
Named repeated-heapify form of the array-facing permutation theorem.
-/
theorem arrayBuildMaxHeapRepeated_perm (xs : List Nat) :
    (arrayBuildMaxHeap xs).Perm xs :=
  arrayBuildMaxHeap_perm xs

/--
Reader-facing correctness theorem for CLRS {lit}`BUILD-MAX-HEAP`: the
bottom-up repeated-{lit}`MAX-HEAPIFY` builder returns an indexed max-heap over
the full array, preserves the input multiset, and preserves array length.
-/
theorem arrayBuildMaxHeap_correct (xs : List Nat) :
    ArrayMaxHeap (arrayBuildMaxHeap xs) (arrayBuildMaxHeap xs).length ∧
      (arrayBuildMaxHeap xs).Perm xs ∧
      (arrayBuildMaxHeap xs).length = xs.length := by
  exact ⟨arrayBuildMaxHeap_isMaxHeap xs, arrayBuildMaxHeap_perm xs,
    buildMaxHeapLoop_length (xs.length / 2) xs xs.length⟩

end Chapter06
end CLRS
