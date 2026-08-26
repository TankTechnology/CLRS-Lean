import CLRSLean.FourthEdition.Chapter_06.Section_06_4_Heapsort

/-!
# CLRS Section 6.5 - Priority Queues

This file gives a functional priority-queue interface on top of the Chapter 6
descending-list heap model, then refines the main CLRS array operations for
maximum, increase-key, extract-max, and delete.  The functional interface
remains a compact scaffold; the reader-facing array theorems track parent/child
indices, key mutation, bubbling, heap-prefix size, length, and permutation.

Main results:

- Theorem {lit}`heapInsert_orderedDesc`: inserting into a heap preserves the
  heap invariant.
- Theorem {lit}`heapInsert_perm`: insertion adds exactly the inserted key.
- Theorem {lit}`heapIncreaseKey_orderedDesc`: increasing one occurrence and
  rebuilding produces a heap.
- Theorem {lit}`heapDelete_orderedDesc`: deleting one occurrence and rebuilding
  produces a heap.
- Theorem {lit}`arrayHeapMaximum?_max`: the root returned by the array-level
  maximum operation bounds every key in the heap prefix.
- Theorems {lit}`ArrayMaxHeap.set_increased_except_up` and
  {lit}`ArrayMaxHeapExceptUp.bubble_step`: the upward-bubbling proof spine for
  array-level {lit}`HEAP-INCREASE-KEY`.
- Theorem {lit}`arrayHeapIncreaseKey?_state_correct`: the full fuelled
  array-level {lit}`HEAP-INCREASE-KEY` wrapper writes a larger key, repeatedly
  bubbles it toward the root, and returns a max-heap with the same backing-list
  length and swapped multiset.
- Theorem {lit}`arrayHeapIncreaseKeyNoBubble?_state_correct`: the no-bubble
  branch of CLRS {lit}`HEAP-INCREASE-KEY` remains as a small readable corollary
  for the immediate-stop case.
- Theorem {lit}`arrayHeapExtractMax?_state_correct`: the CLRS array-level
  extract-max step swaps the root with the last heap cell, shrinks the heap
  prefix, repairs the new root, and returns a state whose prefix is again a
  max-heap while the extracted key is the old maximum.
- Theorem {lit}`arrayHeapDelete?_state_correct`: index-based CLRS
  {lit}`HEAP-DELETE`, implemented by raising the target cell to the current
  root maximum and then extracting the maximum, returns a shrunk heap prefix
  and records the deleted key.

Implementation detail:

- [Array-level MAX-HEAP-INSERT](CLRSLean/FourthEdition/Chapter_06/Section_06_5_Priority_Queues/Insert/)
  appends the new cell, isolates its incoming-edge violation, and reuses the
  established upward-bubbling invariant.

Current gaps:

- Runtime bounds and RAM semantics are deferred.
-/

namespace CLRS
namespace Chapter06

/-! ## Functional priority-queue operations -/

/-- Insert a key into the functional max-priority queue. -/
def heapInsert (x : Nat) (h : List Nat) : List Nat :=
  insertDesc x h

/--
Increase one occurrence of {lit}`old` to {lit}`new`, then rebuild the abstract heap.
If {lit}`old` is absent this inserts {lit}`new`; this total behavior avoids exceptions in
the mathematical interface.
-/
def heapIncreaseKey (old new : Nat) (h : List Nat) : List Nat :=
  buildMaxHeap (new :: h.erase old)

/-- Delete one occurrence of {lit}`key`, then rebuild the abstract heap. -/
def heapDelete (key : Nat) (h : List Nat) : List Nat :=
  buildMaxHeap (h.erase key)

/-! ## Correctness theorems -/

/-- Priority-queue insertion preserves the heap invariant. -/
theorem heapInsert_orderedDesc {x : Nat} {h : List Nat}
    (hh : OrderedDesc h) : OrderedDesc (heapInsert x h) := by
  exact insertDesc_orderedDesc hh

/-- Priority-queue insertion adds exactly the inserted key. -/
theorem heapInsert_perm (x : Nat) (h : List Nat) :
    (heapInsert x h).Perm (x :: h) := by
  exact insertDesc_perm x h

/-- The maximum after insertion is maximal among the old keys and the new key. -/
theorem heapInsert_max {x m : Nat} {h : List Nat}
    (hh : OrderedDesc h) (hmax : heapMaximum? (heapInsert x h) = some m) :
    ∀ y ∈ x :: h, y ≤ m := by
  intro y hy
  have hyheap : y ∈ heapInsert x h :=
    (List.Perm.mem_iff (heapInsert_perm x h)).2 hy
  exact heapMaximum?_max (heapInsert_orderedDesc hh) hmax y hyheap

/-- Increasing a key and rebuilding returns a heap. -/
theorem heapIncreaseKey_orderedDesc (old new : Nat) (h : List Nat) :
    OrderedDesc (heapIncreaseKey old new h) := by
  exact buildMaxHeap_orderedDesc (new :: h.erase old)

/-- Increasing a key preserves exactly the rebuilt multiset specification. -/
theorem heapIncreaseKey_perm (old new : Nat) (h : List Nat) :
    (heapIncreaseKey old new h).Perm (new :: h.erase old) := by
  exact buildMaxHeap_perm (new :: h.erase old)

/-- Deleting one key occurrence and rebuilding returns a heap. -/
theorem heapDelete_orderedDesc (key : Nat) (h : List Nat) :
    OrderedDesc (heapDelete key h) := by
  exact buildMaxHeap_orderedDesc (h.erase key)

/-- Deleting one key occurrence preserves exactly the rebuilt multiset specification. -/
theorem heapDelete_perm (key : Nat) (h : List Nat) :
    (heapDelete key h).Perm (h.erase key) := by
  exact buildMaxHeap_perm (h.erase key)

/-! ## Array-level maximum operation -/

/--
Array-level {lit}`HEAP-MAXIMUM`: return the root when the heap prefix is nonempty
and within the backing list.
-/
def arrayHeapMaximum? (a : List Nat) (heapSize : Nat) : Option Nat :=
  if h : 0 < heapSize ∧ heapSize ≤ a.length then
    some (a[0]'(Nat.lt_of_lt_of_le h.1 h.2))
  else
    none

/-- The array-level maximum returned from the root bounds every heap element. -/
theorem arrayHeapMaximum?_max {a : List Nat} {heapSize m : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hmax : arrayHeapMaximum? a heapSize = some m) :
    ∀ {i : Nat}, (hi : i < heapSize) →
      a[i]'(Nat.lt_of_lt_of_le hi hheap.heapSize_le_length) ≤ m := by
  intro i hi
  have hnonempty : 0 < heapSize := Nat.zero_lt_of_lt hi
  have hcond : 0 < heapSize ∧ heapSize ≤ a.length :=
    ⟨hnonempty, hheap.heapSize_le_length⟩
  have hroot :
      a[0]'(Nat.lt_of_lt_of_le hnonempty hheap.heapSize_le_length) = m := by
    simpa [arrayHeapMaximum?, hcond] using hmax
  rw [← hroot]
  exact hheap.getElem_le_root hi

/-! ## Array-level no-bubble increase-key branch -/

/-- Reading the cell just written by {lit}`List.set`. -/
theorem valAt_set_self {a : List Nat} {i x : Nat} (hi : i < a.length) :
    valAt (a.set i x) i = x := by
  simp [valAt, List.getElem?_set_self hi]

/-- Reading any other cell after {lit}`List.set`. -/
theorem valAt_set_of_ne {a : List Nat} {i k x : Nat} (hki : k ≠ i) :
    valAt (a.set i x) k = valAt a k := by
  simp [valAt, show i ≠ k from Ne.symm hki]

/-!
For {lit}`HEAP-INCREASE-KEY`, the possible violation moves upward.  Unlike
{lit}`MAX-HEAPIFY`, where the possibly bad obligations are the outgoing child
edges of a parent, here the possibly bad obligation is the incoming edge to the
key currently bubbling up.
-/

/--
All heap edges are valid except possibly the edge whose child is
{lit}`badChild`.  The extra field says that the bad child's own children are
already bounded by its parent; this is exactly the fact needed after swapping
the bad child with its parent.
-/
structure ArrayMaxHeapExceptUp (a : List Nat) (heapSize badChild : Nat) : Prop where
  heapSize_le_length : heapSize ≤ a.length
  left_le : ∀ {j : Nat}, j < heapSize → left j < heapSize → left j ≠ badChild →
    valAt a (left j) ≤ valAt a j
  right_le : ∀ {j : Nat}, j < heapSize → right j < heapSize → right j ≠ badChild →
    valAt a (right j) ≤ valAt a j
  bad_children_le_parent : 0 < badChild → badChild < heapSize →
    (∀ _ : left badChild < heapSize,
      valAt a (left badChild) ≤ valAt a (parent badChild)) ∧
    (∀ _ : right badChild < heapSize,
      valAt a (right badChild) ≤ valAt a (parent badChild))

/-- In an upward-exception heap, every non-exempt child is bounded by its parent. -/
theorem ArrayMaxHeapExceptUp.valAt_le_parent_of_ne {a : List Nat}
    {heapSize badChild i : Nat}
    (h : ArrayMaxHeapExceptUp a heapSize badChild)
    (hi : i < heapSize) (hpos : 0 < i) (hne : i ≠ badChild) :
    valAt a i ≤ valAt a (parent i) := by
  let p := parent i
  have hpheap : p < heapSize := Nat.lt_trans (parent_lt_self hpos) hi
  rcases eq_left_or_right_parent hpos with hleft | hright
  · have hchild : left p < heapSize := by simpa [p, hleft.symm] using hi
    have hchild_ne : left p ≠ badChild := by
      simpa [p, hleft.symm] using hne
    have hle := h.left_le hpheap hchild hchild_ne
    simpa [p, hleft.symm] using hle
  · have hchild : right p < heapSize := by simpa [p, hright.symm] using hi
    have hchild_ne : right p ≠ badChild := by
      simpa [p, hright.symm] using hne
    have hle := h.right_le hpheap hchild hchild_ne
    simpa [p, hright.symm] using hle

/-- If the upward exception is absent or already bounded by its parent, the heap is global. -/
theorem ArrayMaxHeapExceptUp.to_global {a : List Nat} {heapSize badChild : Nat}
    (h : ArrayMaxHeapExceptUp a heapSize badChild)
    (hbad : badChild = 0 ∨ valAt a badChild ≤ valAt a (parent badChild)) :
    ArrayMaxHeap a heapSize := by
  refine ⟨h.heapSize_le_length, ?_, ?_⟩
  · intro j hj hl
    have hchild_len : left j < a.length := Nat.lt_of_lt_of_le hl h.heapSize_le_length
    have hparent_len : j < a.length := Nat.lt_of_lt_of_le hj h.heapSize_le_length
    have hval : valAt a (left j) ≤ valAt a j := by
      by_cases hchild : left j = badChild
      · rcases hbad with hroot | hle
        · have hzero : left j = 0 := by simpa [hroot] using hchild
          unfold left at hzero
          omega
        · have hp : parent badChild = j := by
            rw [← hchild, parent_left]
          simpa [hchild, hp] using hle
      · exact h.left_le hj hl hchild
    rw [valAt_eq_getElem a hchild_len, valAt_eq_getElem a hparent_len] at hval
    exact hval
  · intro j hj hr
    have hchild_len : right j < a.length := Nat.lt_of_lt_of_le hr h.heapSize_le_length
    have hparent_len : j < a.length := Nat.lt_of_lt_of_le hj h.heapSize_le_length
    have hval : valAt a (right j) ≤ valAt a j := by
      by_cases hchild : right j = badChild
      · rcases hbad with hroot | hle
        · have hzero : right j = 0 := by simpa [hroot] using hchild
          unfold right at hzero
          omega
        · have hp : parent badChild = j := by
            rw [← hchild, parent_right]
          simpa [hchild, hp] using hle
      · exact h.right_le hj hr hchild
    rw [valAt_eq_getElem a hchild_len, valAt_eq_getElem a hparent_len] at hval
    exact hval

/-- In a global heap, any positive node is bounded by its parent. -/
theorem ArrayMaxHeap.valAt_le_parent {a : List Nat} {heapSize i : Nat}
    (hheap : ArrayMaxHeap a heapSize) (hi : i < heapSize) (hpos : 0 < i) :
    valAt a i ≤ valAt a (parent i) := by
  let p := parent i
  have hpheap : p < heapSize := Nat.lt_trans (parent_lt_self hpos) hi
  have hp_len : p < a.length := Nat.lt_of_lt_of_le hpheap hheap.heapSize_le_length
  rcases eq_left_or_right_parent hpos with hleft | hright
  · have hchild : left p < heapSize := by simpa [p, hleft.symm] using hi
    have hchild_len : left p < a.length :=
      Nat.lt_of_lt_of_le hchild hheap.heapSize_le_length
    have hle := hheap.left_le hpheap hchild
    have hleVal : valAt a (left p) ≤ valAt a p := by
      rw [valAt_eq_getElem a hchild_len, valAt_eq_getElem a hp_len]
      exact hle
    simpa [p, hleft.symm] using hleVal
  · have hchild : right p < heapSize := by simpa [p, hright.symm] using hi
    have hchild_len : right p < a.length :=
      Nat.lt_of_lt_of_le hchild hheap.heapSize_le_length
    have hle := hheap.right_le hpheap hchild
    have hleVal : valAt a (right p) ≤ valAt a p := by
      rw [valAt_eq_getElem a hchild_len, valAt_eq_getElem a hp_len]
      exact hle
    simpa [p, hright.symm] using hleVal

/--
After increasing a key at {lit}`i`, all heap edges are still valid except
possibly the incoming edge to {lit}`i`.  This is the invariant entry point for
the CLRS upward bubbling loop.
-/
theorem ArrayMaxHeap.set_increased_except_up {a : List Nat} {heapSize i key : Nat}
    (hheap : ArrayMaxHeap a heapSize) (hi : i < heapSize)
    (hraise : valAt a i ≤ key) :
    ArrayMaxHeapExceptUp (a.set i key) heapSize i := by
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hheap.heapSize_le_length
  have hlen : heapSize ≤ (a.set i key).length := by
    simpa [List.length_set] using hheap.heapSize_le_length
  have leftVal : ∀ {j : Nat}, j < heapSize → left j < heapSize →
      valAt a (left j) ≤ valAt a j := by
    intro j hj hl
    have hchild_len : left j < a.length :=
      Nat.lt_of_lt_of_le hl hheap.heapSize_le_length
    have hparent_len : j < a.length :=
      Nat.lt_of_lt_of_le hj hheap.heapSize_le_length
    have hold := hheap.left_le hj hl
    rw [← valAt_eq_getElem a hchild_len,
      ← valAt_eq_getElem a hparent_len] at hold
    exact hold
  have rightVal : ∀ {j : Nat}, j < heapSize → right j < heapSize →
      valAt a (right j) ≤ valAt a j := by
    intro j hj hr
    have hchild_len : right j < a.length :=
      Nat.lt_of_lt_of_le hr hheap.heapSize_le_length
    have hparent_len : j < a.length :=
      Nat.lt_of_lt_of_le hj hheap.heapSize_le_length
    have hold := hheap.right_le hj hr
    rw [← valAt_eq_getElem a hchild_len,
      ← valAt_eq_getElem a hparent_len] at hold
    exact hold
  refine ⟨hlen, ?_, ?_, ?_⟩
  · intro j hj hl hchild_ne
    by_cases hparent : j = i
    · subst j
      rw [valAt_set_of_ne (a := a) (i := i) (k := left i) (x := key)
          (left_ne_self i),
        valAt_set_self hi_len]
      exact Nat.le_trans (leftVal hi hl) hraise
    · rw [valAt_set_of_ne (a := a) (i := i) (k := left j) (x := key) hchild_ne,
        valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent]
      exact leftVal hj hl
  · intro j hj hr hchild_ne
    by_cases hparent : j = i
    · subst j
      rw [valAt_set_of_ne (a := a) (i := i) (k := right i) (x := key)
          (right_ne_self i),
        valAt_set_self hi_len]
      exact Nat.le_trans (rightVal hi hr) hraise
    · rw [valAt_set_of_ne (a := a) (i := i) (k := right j) (x := key) hchild_ne,
        valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent]
      exact rightVal hj hr
  · intro hpos _
    have hle_parent := hheap.valAt_le_parent hi hpos
    have hp_ne : parent i ≠ i := ne_of_lt (parent_lt_self hpos)
    constructor
    · intro hl
      rw [valAt_set_of_ne (a := a) (i := i) (k := left i) (x := key)
          (left_ne_self i),
        valAt_set_of_ne (a := a) (i := i) (k := parent i) (x := key) hp_ne]
      exact Nat.le_trans (leftVal hi hl) hle_parent
    · intro hr
      rw [valAt_set_of_ne (a := a) (i := i) (k := right i) (x := key)
          (right_ne_self i),
        valAt_set_of_ne (a := a) (i := i) (k := parent i) (x := key) hp_ne]
      exact Nat.le_trans (rightVal hi hr) hle_parent

/--
One CLRS upward bubbling swap moves the only possible bad incoming edge from
{lit}`i` to {lit}`parent i`.
-/
theorem ArrayMaxHeapExceptUp.bubble_step {a : List Nat} {heapSize i : Nat}
    (h : ArrayMaxHeapExceptUp a heapSize i) (hi : i < heapSize) (hpos : 0 < i)
    (hswap : valAt a (parent i) < valAt a i) :
    ArrayMaxHeapExceptUp (swapAt a i (parent i)) heapSize (parent i) := by
  let p := parent i
  have hpheap : p < heapSize := Nat.lt_trans (parent_lt_self hpos) hi
  have hpi : p < i := parent_lt_self hpos
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi h.heapSize_le_length
  have hp_len : p < a.length := Nat.lt_of_lt_of_le hpheap h.heapSize_le_length
  have hlen : heapSize ≤ (swapAt a i p).length := by
    simpa [p, swapAt_length] using h.heapSize_le_length
  have hp_ne_i : p ≠ i := ne_of_lt hpi
  have hchildren := h.bad_children_le_parent hpos hi
  have hp_old_le_parent : ∀ (hp_pos : 0 < p), valAt a p ≤ valAt a (parent p) := by
    intro hp_pos
    exact h.valAt_le_parent_of_ne hpheap hp_pos hp_ne_i
  refine ⟨hlen, ?_, ?_, ?_⟩
  · intro j hj hl hchild_ne_p
    by_cases hchild_i : left j = i
    · have hjp : j = p := by
        calc
          j = parent (left j) := (parent_left j).symm
          _ = parent i := by rw [hchild_i]
          _ = p := rfl
      rw [hchild_i, hjp]
      rw [valAt_swapAt_left hi_len hp_len, valAt_swapAt_right hi_len hp_len]
      exact Nat.le_of_lt hswap
    · by_cases hj_i : j = i
      · subst j
        have hleft_ne_p : left i ≠ p := by
          unfold left p parent
          omega
        rw [valAt_swapAt_of_ne hi_len hp_len (left_ne_self i) hleft_ne_p,
          valAt_swapAt_left hi_len hp_len]
        exact hchildren.1 hl
      · by_cases hj_p : j = p
        · subst j
          rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hchild_ne_p,
            valAt_swapAt_right hi_len hp_len]
          have hold := h.left_le hpheap hl hchild_i
          exact Nat.le_trans hold (Nat.le_of_lt hswap)
        · rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hchild_ne_p,
            valAt_swapAt_of_ne hi_len hp_len hj_i hj_p]
          exact h.left_le hj hl hchild_i
  · intro j hj hr hchild_ne_p
    by_cases hchild_i : right j = i
    · have hjp : j = p := by
        calc
          j = parent (right j) := (parent_right j).symm
          _ = parent i := by rw [hchild_i]
          _ = p := rfl
      rw [hchild_i, hjp]
      rw [valAt_swapAt_left hi_len hp_len, valAt_swapAt_right hi_len hp_len]
      exact Nat.le_of_lt hswap
    · by_cases hj_i : j = i
      · subst j
        have hright_ne_p : right i ≠ p := by
          unfold right p parent
          omega
        rw [valAt_swapAt_of_ne hi_len hp_len (right_ne_self i) hright_ne_p,
          valAt_swapAt_left hi_len hp_len]
        exact hchildren.2 hr
      · by_cases hj_p : j = p
        · subst j
          rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hchild_ne_p,
            valAt_swapAt_right hi_len hp_len]
          have hold := h.right_le hpheap hr hchild_i
          exact Nat.le_trans hold (Nat.le_of_lt hswap)
        · rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hchild_ne_p,
            valAt_swapAt_of_ne hi_len hp_len hj_i hj_p]
          exact h.right_le hj hr hchild_i
  · intro hp_pos _
    have hparentp_ne_i : parent p ≠ i := by
      have hlt : parent p < i := Nat.lt_trans (parent_lt_self hp_pos) hpi
      exact ne_of_lt hlt
    have hparentp_ne_p : parent p ≠ p := ne_of_lt (parent_lt_self hp_pos)
    have hp_le_gp := hp_old_le_parent hp_pos
    constructor
    · intro hl
      by_cases hchild_i : left p = i
      · rw [hchild_i, valAt_swapAt_left hi_len hp_len]
        rw [valAt_swapAt_of_ne hi_len hp_len hparentp_ne_i hparentp_ne_p]
        exact hp_le_gp
      · have hleft_ne_p : left p ≠ p := left_ne_self p
        rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hleft_ne_p,
          valAt_swapAt_of_ne hi_len hp_len hparentp_ne_i hparentp_ne_p]
        have hold := h.left_le hpheap hl hchild_i
        exact Nat.le_trans hold hp_le_gp
    · intro hr
      by_cases hchild_i : right p = i
      · rw [hchild_i, valAt_swapAt_left hi_len hp_len]
        rw [valAt_swapAt_of_ne hi_len hp_len hparentp_ne_i hparentp_ne_p]
        exact hp_le_gp
      · have hright_ne_p : right p ≠ p := right_ne_self p
        rw [valAt_swapAt_of_ne hi_len hp_len hchild_i hright_ne_p,
          valAt_swapAt_of_ne hi_len hp_len hparentp_ne_i hparentp_ne_p]
        have hold := h.right_le hpheap hr hchild_i
        exact Nat.le_trans hold hp_le_gp

/--
Fuelled upward bubbling loop for array-level {lit}`HEAP-INCREASE-KEY`.  The
fuel is bounded by the starting index, since each swap moves to the strict
parent.
-/
def arrayHeapIncreaseKeyBubbleUpFuel : Nat → List Nat → Nat → Nat → List Nat
  | 0, a, _heapSize, _i => a
  | fuel + 1, a, heapSize, i =>
      if _ : 0 < i then
        if valAt a (parent i) < valAt a i then
          arrayHeapIncreaseKeyBubbleUpFuel fuel (swapAt a i (parent i)) heapSize (parent i)
        else
          a
      else
        a

/-- The upward bubbling loop preserves the backing-list length. -/
theorem arrayHeapIncreaseKeyBubbleUpFuel_length (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (arrayHeapIncreaseKeyBubbleUpFuel fuel a heapSize i).length = a.length := by
  induction fuel generalizing a i with
  | zero =>
      simp [arrayHeapIncreaseKeyBubbleUpFuel]
  | succ fuel ih =>
      by_cases hpos : 0 < i
      · by_cases hswap : valAt a (parent i) < valAt a i
        · simp [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap,
            ih (a := swapAt a i (parent i)) (i := parent i), swapAt_length]
        · simp [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap]
      · simp [arrayHeapIncreaseKeyBubbleUpFuel, hpos]

/-- The upward bubbling loop only swaps cells, so it preserves the multiset. -/
theorem arrayHeapIncreaseKeyBubbleUpFuel_perm (fuel : Nat) (a : List Nat)
    (heapSize i : Nat) :
    (arrayHeapIncreaseKeyBubbleUpFuel fuel a heapSize i).Perm a := by
  induction fuel generalizing a i with
  | zero =>
      simp [arrayHeapIncreaseKeyBubbleUpFuel]
  | succ fuel ih =>
      by_cases hpos : 0 < i
      · by_cases hswap : valAt a (parent i) < valAt a i
        · have hrec := ih (a := swapAt a i (parent i)) (i := parent i)
          exact (by
            simpa [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap] using
              hrec.trans (swapAt_perm a i (parent i)))
        · simp [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap]
      · simp [arrayHeapIncreaseKeyBubbleUpFuel, hpos]

/--
Enough upward-bubbling fuel discharges the upward exception and restores a
global heap.
-/
theorem ArrayMaxHeapExceptUp.bubbleUpFuel_global {fuel : Nat} {a : List Nat}
    {heapSize i : Nat} (h : ArrayMaxHeapExceptUp a heapSize i)
    (hi : i < heapSize) (hfuel : i ≤ fuel) :
    ArrayMaxHeap (arrayHeapIncreaseKeyBubbleUpFuel fuel a heapSize i) heapSize := by
  induction fuel generalizing a heapSize i with
  | zero =>
      have hzero : i = 0 := by omega
      have hglobal : ArrayMaxHeap a heapSize := h.to_global (Or.inl hzero)
      simpa [arrayHeapIncreaseKeyBubbleUpFuel] using hglobal
  | succ fuel ih =>
      by_cases hpos : 0 < i
      · by_cases hswap : valAt a (parent i) < valAt a i
        · have hpheap : parent i < heapSize := Nat.lt_trans (parent_lt_self hpos) hi
          have hp_le_fuel : parent i ≤ fuel := by
            have hpi : parent i < i := parent_lt_self hpos
            omega
          have hnext : ArrayMaxHeapExceptUp (swapAt a i (parent i)) heapSize (parent i) :=
            h.bubble_step hi hpos hswap
          have hrec := ih (a := swapAt a i (parent i)) (heapSize := heapSize)
            (i := parent i) hnext hpheap hp_le_fuel
          simpa [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap] using hrec
        · have hle : valAt a i ≤ valAt a (parent i) := Nat.le_of_not_lt hswap
          have hglobal : ArrayMaxHeap a heapSize := h.to_global (Or.inr hle)
          simpa [arrayHeapIncreaseKeyBubbleUpFuel, hpos, hswap] using hglobal
      · have hzero : i = 0 := Nat.eq_zero_of_not_pos hpos
        have hglobal : ArrayMaxHeap a heapSize := h.to_global (Or.inl hzero)
        simpa [arrayHeapIncreaseKeyBubbleUpFuel, hpos] using hglobal

/-- Array-level CLRS {lit}`HEAP-INCREASE-KEY`: write the key and bubble it upward. -/
def arrayHeapIncreaseKey? (a : List Nat) (heapSize i key : Nat) : Option (List Nat) :=
  if _h : i < heapSize ∧ heapSize ≤ a.length ∧ valAt a i ≤ key then
    some (arrayHeapIncreaseKeyBubbleUpFuel i (a.set i key) heapSize i)
  else
    none

/-- State-correctness theorem for array-level {lit}`HEAP-INCREASE-KEY`. -/
theorem arrayHeapIncreaseKey?_state_correct {a rest : List Nat} {heapSize i key : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapIncreaseKey? a heapSize i key = some rest) :
    i < heapSize ∧
      heapSize ≤ a.length ∧
      valAt a i ≤ key ∧
      ArrayMaxHeap rest heapSize ∧
      rest.length = a.length ∧
      rest.Perm (a.set i key) := by
  unfold arrayHeapIncreaseKey? at hres
  by_cases hcond : i < heapSize ∧ heapSize ≤ a.length ∧ valAt a i ≤ key
  · simp [hcond] at hres
    subst rest
    have hentry : ArrayMaxHeapExceptUp (a.set i key) heapSize i :=
      hheap.set_increased_except_up hcond.1 hcond.2.2
    have hrest_heap :
        ArrayMaxHeap (arrayHeapIncreaseKeyBubbleUpFuel i (a.set i key) heapSize i)
          heapSize :=
      hentry.bubbleUpFuel_global hcond.1 (Nat.le_refl i)
    have hlen := arrayHeapIncreaseKeyBubbleUpFuel_length i (a.set i key) heapSize i
    have hperm := arrayHeapIncreaseKeyBubbleUpFuel_perm i (a.set i key) heapSize i
    refine ⟨hcond.1, hcond.2.1, hcond.2.2, hrest_heap, ?_, hperm⟩
    simpa [List.length_set] using hlen
  · simp [hcond] at hres

/--
Core no-bubble lemma for CLRS {lit}`HEAP-INCREASE-KEY`.  If increasing a heap
cell leaves it below its parent, the array is already a max-heap after the
write, so the upward while-loop would stop immediately.
-/
theorem ArrayMaxHeap.set_increased_no_bubble {a : List Nat} {heapSize i key : Nat}
    (hheap : ArrayMaxHeap a heapSize) (hi : i < heapSize)
    (hraise : valAt a i ≤ key)
    (hnobubble : i = 0 ∨ key ≤ valAt a (parent i)) :
    ArrayMaxHeap (a.set i key) heapSize := by
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hheap.heapSize_le_length
  have hlen : heapSize ≤ (a.set i key).length := by
    simpa [List.length_set] using hheap.heapSize_le_length
  have leftVal : ∀ {j : Nat}, j < heapSize → left j < heapSize →
      valAt a (left j) ≤ valAt a j := by
    intro j hj hl
    have hchild_len : left j < a.length :=
      Nat.lt_of_lt_of_le hl hheap.heapSize_le_length
    have hparent_len : j < a.length :=
      Nat.lt_of_lt_of_le hj hheap.heapSize_le_length
    have hold := hheap.left_le hj hl
    rw [← valAt_eq_getElem a hchild_len,
      ← valAt_eq_getElem a hparent_len] at hold
    exact hold
  have rightVal : ∀ {j : Nat}, j < heapSize → right j < heapSize →
      valAt a (right j) ≤ valAt a j := by
    intro j hj hr
    have hchild_len : right j < a.length :=
      Nat.lt_of_lt_of_le hr hheap.heapSize_le_length
    have hparent_len : j < a.length :=
      Nat.lt_of_lt_of_le hj hheap.heapSize_le_length
    have hold := hheap.right_le hj hr
    rw [← valAt_eq_getElem a hchild_len,
      ← valAt_eq_getElem a hparent_len] at hold
    exact hold
  refine ⟨hlen, ?_, ?_⟩
  · intro j hj hl
    have hchild_len : left j < (a.set i key).length := Nat.lt_of_lt_of_le hl hlen
    have hparent_len : j < (a.set i key).length := Nat.lt_of_lt_of_le hj hlen
    have hval : valAt (a.set i key) (left j) ≤ valAt (a.set i key) j := by
      by_cases hchild : left j = i
      · rw [hchild, valAt_set_self hi_len]
        have hparent_ne : j ≠ i := by
          rw [← hchild]
          unfold left
          omega
        rw [valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent_ne]
        rcases hnobubble with hroot | hle_parent
        · have hleft_zero : left j = 0 := by simpa [hroot] using hchild
          unfold left at hleft_zero
          omega
        · have hp : parent i = j := by
            rw [← hchild, parent_left]
          simpa [hp] using hle_parent
      · by_cases hparent : j = i
        · subst j
          rw [valAt_set_of_ne (a := a) (i := i) (k := left i) (x := key)
              (left_ne_self i),
            valAt_set_self hi_len]
          exact Nat.le_trans (leftVal hi hl) hraise
        · rw [valAt_set_of_ne (a := a) (i := i) (k := left j) (x := key) hchild,
            valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent]
          exact leftVal hj hl
    rw [valAt_eq_getElem (a.set i key) hchild_len,
      valAt_eq_getElem (a.set i key) hparent_len] at hval
    exact hval
  · intro j hj hr
    have hchild_len : right j < (a.set i key).length := Nat.lt_of_lt_of_le hr hlen
    have hparent_len : j < (a.set i key).length := Nat.lt_of_lt_of_le hj hlen
    have hval : valAt (a.set i key) (right j) ≤ valAt (a.set i key) j := by
      by_cases hchild : right j = i
      · rw [hchild, valAt_set_self hi_len]
        have hparent_ne : j ≠ i := by
          rw [← hchild]
          unfold right
          omega
        rw [valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent_ne]
        rcases hnobubble with hroot | hle_parent
        · have hright_zero : right j = 0 := by simpa [hroot] using hchild
          unfold right at hright_zero
          omega
        · have hp : parent i = j := by
            rw [← hchild, parent_right]
          simpa [hp] using hle_parent
      · by_cases hparent : j = i
        · subst j
          rw [valAt_set_of_ne (a := a) (i := i) (k := right i) (x := key)
              (right_ne_self i),
            valAt_set_self hi_len]
          exact Nat.le_trans (rightVal hi hr) hraise
        · rw [valAt_set_of_ne (a := a) (i := i) (k := right j) (x := key) hchild,
            valAt_set_of_ne (a := a) (i := i) (k := j) (x := key) hparent]
          exact rightVal hj hr
    rw [valAt_eq_getElem (a.set i key) hchild_len,
      valAt_eq_getElem (a.set i key) hparent_len] at hval
    exact hval

/--
Array-level no-bubble branch of CLRS {lit}`HEAP-INCREASE-KEY`: write the new
key at index {lit}`i` when the key is larger than the old key but still no
larger than its parent, so the upward repair loop stops immediately.
-/
def arrayHeapIncreaseKeyNoBubble? (a : List Nat) (heapSize i key : Nat) :
    Option (List Nat) :=
  if _h : i < heapSize ∧ heapSize ≤ a.length ∧ valAt a i ≤ key ∧
      (i = 0 ∨ key ≤ valAt a (parent i)) then
    some (a.set i key)
  else
    none

/-- State-correctness theorem for the no-bubble branch of array-level increase-key. -/
theorem arrayHeapIncreaseKeyNoBubble?_state_correct {a rest : List Nat}
    {heapSize i key : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapIncreaseKeyNoBubble? a heapSize i key = some rest) :
    i < heapSize ∧
      heapSize ≤ a.length ∧
      valAt a i ≤ key ∧
      (i = 0 ∨ key ≤ valAt a (parent i)) ∧
      ArrayMaxHeap rest heapSize ∧
      rest.length = a.length ∧
      valAt rest i = key ∧
      (∀ {k : Nat}, k ≠ i → valAt rest k = valAt a k) := by
  unfold arrayHeapIncreaseKeyNoBubble? at hres
  by_cases hcond :
      i < heapSize ∧ heapSize ≤ a.length ∧ valAt a i ≤ key ∧
        (i = 0 ∨ key ≤ valAt a (parent i))
  · simp [hcond] at hres
    subst rest
    have hi_len : i < a.length := Nat.lt_of_lt_of_le hcond.1 hcond.2.1
    refine ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, ?_, ?_, ?_, ?_⟩
    · exact hheap.set_increased_no_bubble hcond.1 hcond.2.2.1 hcond.2.2.2
    · simp [List.length_set]
    · exact valAt_set_self hi_len
    · intro k hk
      exact valAt_set_of_ne (a := a) (i := i) (k := k) (x := key) hk
  · simp [hcond] at hres

/-! ## Array-level extract-max -/

/--
Array-level {lit}`HEAP-EXTRACT-MAX`.  The returned triple is the extracted
maximum, the backing array after the CLRS root/last swap and root heapify, and
the new heap prefix size.
-/
def arrayHeapExtractMax? (a : List Nat) (heapSize : Nat) :
    Option (Nat × List Nat × Nat) :=
  if h : 0 < heapSize ∧ heapSize ≤ a.length then
    let newHeapSize := heapSize - 1
    let maximum := a[0]'(Nat.lt_of_lt_of_le h.1 h.2)
    let moved := swapAt a 0 newHeapSize
    let repaired := maxHeapifyFuel newHeapSize moved newHeapSize 0
    some (maximum, repaired, newHeapSize)
  else
    none

/--
State-correctness theorem for the array-level CLRS {lit}`HEAP-EXTRACT-MAX`
step.  The array keeps the same length and multiset, the heap prefix shrinks by
one and is repaired into a max-heap, the returned key bounds the old heap prefix,
and that key is stored at the first cell outside the new heap prefix.
-/
theorem arrayHeapExtractMax?_state_correct {a : List Nat} {heapSize m : Nat}
    {rest : List Nat} {newHeapSize : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapExtractMax? a heapSize = some (m, rest, newHeapSize)) :
    0 < heapSize ∧
      newHeapSize + 1 = heapSize ∧
      ArrayMaxHeap rest newHeapSize ∧
      rest.length = a.length ∧
      rest.Perm a ∧
      (∀ {i : Nat}, i < heapSize → valAt a i ≤ m) ∧
      newHeapSize < rest.length ∧
      valAt rest newHeapSize = m := by
  unfold arrayHeapExtractMax? at hres
  by_cases hcond : 0 < heapSize ∧ heapSize ≤ a.length
  · simp [hcond] at hres
    rcases hres with ⟨hm, hrest_eq, hnew_eq⟩
    subst m
    subst rest
    subst newHeapSize
    set newSize := heapSize - 1
    have hsize_eq : newSize + 1 = heapSize := by
      dsimp [newSize]
      omega
    have hlen_swapped : newSize ≤ (swapAt a 0 newSize).length := by
      rw [swapAt_length]
      dsimp [newSize]
      omega
    have hrest_len :
        (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0).length =
          a.length := by
      rw [maxHeapifyFuel_length, swapAt_length]
    have hrest_perm :
        (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0).Perm a := by
      exact (maxHeapifyFuel_perm newSize (swapAt a 0 newSize) newSize 0).trans
        (swapAt_perm a 0 newSize)
    have h0_len : 0 < a.length := Nat.lt_of_lt_of_le hcond.1 hcond.2
    have hlast_len : newSize < a.length := by
      dsimp [newSize]
      omega
    have hroot_val :
        valAt a 0 = a[0]'(Nat.lt_of_lt_of_le hcond.1 hcond.2) := by
      rw [valAt_eq_getElem a h0_len]
    have hmax_bound :
        ∀ {i : Nat}, i < heapSize →
          valAt a i ≤ a[0]'(Nat.lt_of_lt_of_le hcond.1 hcond.2) := by
      intro i hi
      rw [← hroot_val]
      exact hheap.valAt_le_root hi
    have hheap_rest :
        ArrayMaxHeap (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0)
          newSize := by
      by_cases hnew : 0 < newSize
      · have hheap' : ArrayMaxHeap a (newSize + 1) := by
          rwa [hsize_eq]
        have hexcept : ArrayMaxHeapExcept (swapAt a 0 newSize) newSize 0 :=
          ArrayMaxHeapExcept.of_swap_root_last
            (a := a) (newHeapSize := newSize) hheap'
        exact maxHeapifyFuel_root_isMaxHeap
          (fuel := newSize) hexcept hnew (Nat.le_refl newSize)
      · have hzero : newSize = 0 := by omega
        rw [hzero]
        refine ⟨Nat.zero_le _, ?_, ?_⟩ <;> intro i hi hchild <;> omega
    have hstored :
        valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize =
          a[0]'(Nat.lt_of_lt_of_le hcond.1 hcond.2) := by
      by_cases hnew : 0 < newSize
      · have hheapify_read :
            valAt (maxHeapifyFuel newSize (swapAt a 0 newSize) newSize 0) newSize =
              valAt (swapAt a 0 newSize) newSize :=
          maxHeapifyFuel_valAt_of_heapSize_le
            (fuel := newSize) (a := swapAt a 0 newSize) (heapSize := newSize)
            (i := 0) (k := newSize) hlen_swapped hnew (Nat.le_refl newSize)
        have hswap_read :
            valAt (swapAt a 0 newSize) newSize = valAt a 0 :=
          valAt_swapAt_right h0_len hlast_len
        rw [hheapify_read, hswap_read, hroot_val]
      · have hzero : newSize = 0 := by omega
        rw [hzero]
        have hswap_read : valAt (swapAt a 0 0) 0 = valAt a 0 :=
          valAt_swapAt_right h0_len h0_len
        simpa [maxHeapifyFuel, hroot_val] using hswap_read
    refine ⟨hcond.1, hsize_eq, hheap_rest, hrest_len, hrest_perm, hmax_bound, ?_, hstored⟩
    rw [hrest_len]
    exact hlast_len
  · simp [hcond] at hres

/-! ## Array-level delete -/

/--
Array-level CLRS {lit}`HEAP-DELETE`, expressed through the usual priority-queue
recipe: raise the target cell to the current root maximum, then extract the
maximum.  In a finite natural-number model, the old root key is enough: it is a
heap-prefix upper bound, so replacing the target by that key makes the target
eligible for the subsequent extract-max step.
-/
def arrayHeapDelete? (a : List Nat) (heapSize i : Nat) :
    Option (Nat × List Nat × Nat) :=
  if _h : i < heapSize ∧ heapSize ≤ a.length then
    match arrayHeapIncreaseKey? a heapSize i (valAt a 0) with
    | some raised =>
        match arrayHeapExtractMax? raised heapSize with
        | some (_removed, rest, newHeapSize) => some (valAt a i, rest, newHeapSize)
        | none => none
    | none => none
  else
    none

/--
State-correctness theorem for array-level {lit}`HEAP-DELETE`.  The returned
heap prefix has size one less than the old prefix, is a max-heap, and the
backing list is exactly the permutation produced by replacing the deleted cell
with the old root maximum before the extract step.
-/
theorem arrayHeapDelete?_state_correct {a rest : List Nat}
    {heapSize i deleted newHeapSize : Nat}
    (hheap : ArrayMaxHeap a heapSize)
    (hres : arrayHeapDelete? a heapSize i = some (deleted, rest, newHeapSize)) :
    i < heapSize ∧
      heapSize ≤ a.length ∧
      deleted = valAt a i ∧
      newHeapSize + 1 = heapSize ∧
      ArrayMaxHeap rest newHeapSize ∧
      rest.length = a.length ∧
      rest.Perm (a.set i (valAt a 0)) ∧
      (∀ {k : Nat}, k < heapSize → valAt a k ≤ valAt a 0) := by
  unfold arrayHeapDelete? at hres
  by_cases hcond : i < heapSize ∧ heapSize ≤ a.length
  · simp [hcond] at hres
    cases hinc : arrayHeapIncreaseKey? a heapSize i (valAt a 0) with
    | none =>
        simp [hinc] at hres
    | some raised =>
        simp [hinc] at hres
        cases hext : arrayHeapExtractMax? raised heapSize with
        | none =>
            simp [hext] at hres
        | some extracted =>
            rcases extracted with ⟨removed, extractedRest, extractedNewHeapSize⟩
            simp [hext] at hres
            rcases hres with ⟨hdeleted, hrest, hnew⟩
            subst deleted
            subst rest
            subst newHeapSize
            have hinc_correct := arrayHeapIncreaseKey?_state_correct
              (a := a) (rest := raised) (heapSize := heapSize) (i := i)
              (key := valAt a 0) hheap hinc
            have hext_correct := arrayHeapExtractMax?_state_correct
              (a := raised) (heapSize := heapSize) (m := removed)
              (rest := extractedRest) (newHeapSize := extractedNewHeapSize)
              hinc_correct.2.2.2.1 hext
            have hroot_bound :
                ∀ {k : Nat}, k < heapSize → valAt a k ≤ valAt a 0 := by
              intro k hk
              exact hheap.valAt_le_root hk
            have hperm : extractedRest.Perm (a.set i (valAt a 0)) :=
              hext_correct.2.2.2.2.1.trans hinc_correct.2.2.2.2.2
            refine ⟨hcond.1, hcond.2, rfl, hext_correct.2.1,
              hext_correct.2.2.1, ?_, hperm, hroot_bound⟩
            exact hext_correct.2.2.2.1.trans hinc_correct.2.2.2.2.1
  · simp [hcond] at hres

end Chapter06
end CLRS
