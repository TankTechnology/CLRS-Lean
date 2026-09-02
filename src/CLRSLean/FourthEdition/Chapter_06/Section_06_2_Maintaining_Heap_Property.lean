import CLRSLean.FourthEdition.Chapter_06.Section_06_1_Heaps

/-!
# CLRS Section 6.2 - Maintaining the Heap Property

This section isolates the executable pieces around CLRS {lit}`MAX-HEAPIFY`.

Main results:

- Theorem {lit}`swapAt_perm`: swapping two array cells preserves the multiset
  of elements.
- Theorems {lit}`valAt_swapAt_left` and {lit}`valAt_swapAt_right`: after an
  in-bounds swap, the two exchanged cells contain each other's old values.
- Theorem {lit}`valAt_swapAt_of_ne`: every non-swapped index is unchanged.
- Theorem {lit}`maxHeapifyFuel_perm`: the fuelled executable heapify loop
  preserves the multiset of elements.
- Theorem {lit}`maxHeapifyFuel_valAt_of_heapSize_le`: fuelled heapify does not
  change cells outside the heap prefix.
- Theorems {lit}`valAt_i_le_maxChildIndex`,
  {lit}`valAt_left_le_maxChildIndex`, and
  {lit}`valAt_right_le_maxChildIndex`: the CLRS {lit}`largest` choice is locally
  maximal among the root and in-heap children.
- Theorem {lit}`arrayMaxHeap_of_except_of_maxChildIndex_self`: the no-swap
  branch of {lit}`MAX-HEAPIFY` repairs the only potentially bad parent.
- Theorem {lit}`arrayMaxHeapExceptFrom_after_swap_at_root`: a nontrivial swap
  repairs the current parent and moves the local exception down to the selected
  child.
- Theorem {lit}`maxHeapifyFuel_swap_branch_repair`: in the nontrivial
  recursive branch, swapping with the selected child and recursively heapifying
  repairs the original localized heap.
- Theorem {lit}`arrayMaxHeapFrom_of_maxHeapifyFuel_succ`: one fuelled heapify
  step is correct once the recursive branch supplies the child postcondition.
- Theorem {lit}`maxHeapifyFuel_repair_subtree`: enough fuel recursively repairs
  the localized subtree rooted at {lit}`i`.
- Theorem {lit}`maxHeapifyFuel_root_isMaxHeap`: root heapify with enough fuel
  produces a global max-heap.

Remaining refinements:

- The recursive fuelled {lit}`MAX-HEAPIFY` repair theorem is proved and consumed
  by Section 6.3's bottom-up {lit}`BUILD-MAX-HEAP` and Section 6.4's in-place
  {lit}`HEAPSORT` loop.  Later work can add a shared imperative array semantics
  and line-by-line runtime costs.
-/

namespace CLRS
namespace Chapter06

/-! ## Swaps and fuelled {lit}`MAX-HEAPIFY` -/

/-- Read an array cell with fallback zero outside the list. -/
def valAt (a : List Nat) (i : Nat) : Nat :=
  a.getD i 0

/-- Inside bounds, {lit}`valAt` is the ordinary list-backed array read. -/
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

/-- After an in-bounds swap, every index outside the swapped pair is unchanged. -/
theorem valAt_swapAt_of_ne {a : List Nat} {i j k : Nat}
    (hi : i < a.length) (hj : j < a.length)
    (hki : k ≠ i) (hkj : k ≠ j) :
    valAt (swapAt a i j) k = valAt a k := by
  unfold swapAt
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  unfold valAt
  change (((a.set i a[j]).set j a[i])[k]?.getD 0 = a[k]?.getD 0)
  rw [List.getElem?_set]
  simp [show j ≠ k from Ne.symm hkj]
  rw [List.getElem?_set]
  simp [show i ≠ k from Ne.symm hki]

/--
Path invariant for recursive heapify.  If the current bad node is below the
localized root {lit}`start`, the value at its parent already dominates both
children of the bad node.  This is the extra fact that keeps the incoming edge
valid when the bad node swaps with its largest child.
-/
def BadChildrenLeParent (a : List Nat) (heapSize start i : Nat) : Prop :=
  start < i →
    (∀ _ : left i < heapSize, valAt a (left i) ≤ valAt a (parent i)) ∧
    (∀ _ : right i < heapSize, valAt a (right i) ≤ valAt a (parent i))

/-- At the localized root, the path-bound condition is vacuous. -/
theorem BadChildrenLeParent.self (a : List Nat) (heapSize i : Nat) :
    BadChildrenLeParent a heapSize i i := by
  intro h
  omega

/-- Choose between a current largest index and a candidate child. -/
def largerIndex (a : List Nat) (heapSize current candidate : Nat) : Nat :=
  if candidate < heapSize then
    if valAt a current < valAt a candidate then candidate else current
  else
    current

/-- The CLRS choice of the largest among {lit}`i`, {lit}`left i`, and {lit}`right i`. -/
def maxChildIndex (a : List Nat) (heapSize i : Nat) : Nat :=
  largerIndex a heapSize (largerIndex a heapSize i (left i)) (right i)

/-- A {lit}`largerIndex` result is at least the current index's key. -/
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

/-- If the candidate is in the heap, a {lit}`largerIndex` result is at least it. -/
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

/-- If the root is inside the heap, the CLRS {lit}`largest` index is inside too. -/
theorem maxChildIndex_lt_heapSize {a : List Nat} {heapSize i : Nat}
    (hi : i < heapSize) : maxChildIndex a heapSize i < heapSize := by
  unfold maxChildIndex
  exact largerIndex_lt_heapSize (largerIndex_lt_heapSize hi)

/-- A {lit}`largerIndex` call returns either the current index or the candidate. -/
theorem largerIndex_eq_current_or_candidate (a : List Nat)
    (heapSize current candidate : Nat) :
    largerIndex a heapSize current candidate = current ∨
      largerIndex a heapSize current candidate = candidate := by
  unfold largerIndex
  by_cases hc : candidate < heapSize
  · simp [hc]
    by_cases hlt : valAt a current < valAt a candidate
    · simp [hlt]
    · simp [hlt]
  · simp [hc]

/--
The CLRS {lit}`largest` index is one of the root, left child, or right child.
-/
theorem maxChildIndex_eq_self_or_left_or_right (a : List Nat)
    (heapSize i : Nat) :
    maxChildIndex a heapSize i = i ∨
      maxChildIndex a heapSize i = left i ∨
      maxChildIndex a heapSize i = right i := by
  unfold maxChildIndex
  rcases largerIndex_eq_current_or_candidate a heapSize i (left i) with hleft | hleft
  · rcases largerIndex_eq_current_or_candidate a heapSize
        (largerIndex a heapSize i (left i)) (right i) with hright | hright
    · left
      simpa [hleft] using hright
    · right
      right
      exact hright
  · rcases largerIndex_eq_current_or_candidate a heapSize
        (largerIndex a heapSize i (left i)) (right i) with hright | hright
    · right
      left
      simpa [hleft] using hright
    · right
      right
      exact hright

/-- If {lit}`MAX-HEAPIFY` swaps, the selected index is one of the two children. -/
theorem maxChildIndex_eq_left_or_right_of_ne {a : List Nat} {heapSize i : Nat}
    (h : maxChildIndex a heapSize i ≠ i) :
    maxChildIndex a heapSize i = left i ∨
      maxChildIndex a heapSize i = right i := by
  rcases maxChildIndex_eq_self_or_left_or_right a heapSize i with hself | hchild
  · exact False.elim (h hself)
  · exact hchild

/-- A swapping {lit}`MAX-HEAPIFY` step moves strictly down the array heap. -/
theorem lt_maxChildIndex_of_ne {a : List Nat} {heapSize i : Nat}
    (h : maxChildIndex a heapSize i ≠ i) : i < maxChildIndex a heapSize i := by
  rcases maxChildIndex_eq_left_or_right_of_ne h with hleft | hright
  · rw [hleft]
    unfold left
    omega
  · rw [hright]
    unfold right
    omega

/-- A nontrivial heapify step strictly decreases the remaining index distance. -/
theorem heapSize_sub_maxChildIndex_lt_of_ne {a : List Nat} {heapSize i : Nat}
    (hi : i < heapSize) (h : maxChildIndex a heapSize i ≠ i) :
    heapSize - maxChildIndex a heapSize i < heapSize - i := by
  have hdown : i < maxChildIndex a heapSize i := lt_maxChildIndex_of_ne h
  have hheap : maxChildIndex a heapSize i < heapSize :=
    maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  omega

/-- The selected CLRS {lit}`largest` key is at least the original root key. -/
theorem valAt_i_le_maxChildIndex (a : List Nat) (heapSize i : Nat) :
    valAt a i ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_current_le_largerIndex a heapSize i (left i))
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS {lit}`largest` key is at least the left child's key. -/
theorem valAt_left_le_maxChildIndex {a : List Nat} {heapSize i : Nat}
    (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a (maxChildIndex a heapSize i) := by
  unfold maxChildIndex
  exact Nat.le_trans (valAt_candidate_le_largerIndex (a := a) (current := i) hl)
    (valAt_current_le_largerIndex a heapSize
      (largerIndex a heapSize i (left i)) (right i))

/-- The selected CLRS {lit}`largest` key is at least the right child's key. -/
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
After a nontrivial heapify swap, the value moved into {lit}`i` dominates the
old left child.
-/
theorem valAt_swapAt_i_ge_left {a : List Nat} {heapSize i : Nat}
    (hlen : heapSize ≤ a.length) (hi : i < heapSize)
    (_hneq : maxChildIndex a heapSize i ≠ i) (hl : left i < heapSize) :
    valAt (swapAt a i (maxChildIndex a heapSize i)) (left i) ≤
      valAt (swapAt a i (maxChildIndex a heapSize i)) i := by
  let largest := maxChildIndex a heapSize i
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hlargest_len : largest < a.length := Nat.lt_of_lt_of_le hlargest_heap hlen
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hlen
  have hparent :
      valAt (swapAt a i largest) i = valAt a largest :=
    valAt_swapAt_left hi_len hlargest_len
  by_cases hleft : left i = largest
  · have hchild :
        valAt (swapAt a i largest) (left i) = valAt a i := by
      simpa [hleft] using valAt_swapAt_right hi_len hlargest_len
    rw [hchild, hparent]
    simpa [largest] using valAt_i_le_maxChildIndex a heapSize i
  · have hchild :
        valAt (swapAt a i largest) (left i) = valAt a (left i) := by
      exact valAt_swapAt_of_ne hi_len hlargest_len (left_ne_self i) hleft
    rw [hchild, hparent]
    simpa [largest] using valAt_left_le_maxChildIndex (a := a) (heapSize := heapSize)
      (i := i) hl

/--
After a nontrivial heapify swap, the value moved into {lit}`i` dominates the
old right child.
-/
theorem valAt_swapAt_i_ge_right {a : List Nat} {heapSize i : Nat}
    (hlen : heapSize ≤ a.length) (hi : i < heapSize)
    (_hneq : maxChildIndex a heapSize i ≠ i) (hr : right i < heapSize) :
    valAt (swapAt a i (maxChildIndex a heapSize i)) (right i) ≤
      valAt (swapAt a i (maxChildIndex a heapSize i)) i := by
  let largest := maxChildIndex a heapSize i
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hlargest_len : largest < a.length := Nat.lt_of_lt_of_le hlargest_heap hlen
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hlen
  have hparent :
      valAt (swapAt a i largest) i = valAt a largest :=
    valAt_swapAt_left hi_len hlargest_len
  by_cases hright : right i = largest
  · have hchild :
        valAt (swapAt a i largest) (right i) = valAt a i := by
      simpa [hright] using valAt_swapAt_right hi_len hlargest_len
    rw [hchild, hparent]
    simpa [largest] using valAt_i_le_maxChildIndex a heapSize i
  · have hchild :
        valAt (swapAt a i largest) (right i) = valAt a (right i) := by
      exact valAt_swapAt_of_ne hi_len hlargest_len (right_ne_self i) hright
    rw [hchild, hparent]
    simpa [largest] using valAt_right_le_maxChildIndex (a := a) (heapSize := heapSize)
      (i := i) hr

/--
One nontrivial {lit}`MAX-HEAPIFY` swap repairs the current parent and moves the
single local exception down to the selected child.  This is the local
swap-branch certificate used by the recursive proof.
-/
theorem arrayMaxHeapExceptFrom_after_swap_at_root {a : List Nat} {heapSize i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize i i)
    (hi : i < heapSize) (hneq : maxChildIndex a heapSize i ≠ i) :
    ArrayMaxHeapExceptFrom
      (swapAt a i (maxChildIndex a heapSize i)) heapSize i
      (maxChildIndex a heapSize i) := by
  let largest := maxChildIndex a heapSize i
  have hlen_swapped : heapSize ≤ (swapAt a i largest).length := by
    simpa [largest, swapAt_length] using hexcept.heapSize_le_length
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hexcept.heapSize_le_length
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hlargest_len : largest < a.length :=
    Nat.lt_of_lt_of_le hlargest_heap hexcept.heapSize_le_length
  have hlargest_child : largest = left i ∨ largest = right i := by
    simpa [largest] using maxChildIndex_eq_left_or_right_of_ne hneq
  refine ⟨hlen_swapped, ?_, ?_⟩
  · intro j hij hj hbad hl
    by_cases hji : j = i
    · subst j
      have hval := valAt_swapAt_i_ge_left
        (a := a) (heapSize := heapSize) (i := i)
        hexcept.heapSize_le_length hi hneq hl
      rw [valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hl hlen_swapped),
        valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
      simpa [largest] using hval
    · have hleft_ne_i : left j ≠ i := by
        intro hEq
        unfold left at hEq
        omega
      have hleft_ne_largest : left j ≠ largest := by
        intro hEq
        rcases hlargest_child with hleft | hright
        · have : left j = left i := by simpa [hleft] using hEq
          unfold left at this
          omega
        · have : left j = right i := by simpa [hright] using hEq
          unfold left right at this
          omega
      have hchild_read :
          valAt (swapAt a i largest) (left j) = valAt a (left j) :=
        valAt_swapAt_of_ne hi_len hlargest_len hleft_ne_i hleft_ne_largest
      have hparent_read :
          valAt (swapAt a i largest) j = valAt a j :=
        valAt_swapAt_of_ne hi_len hlargest_len hji hbad
      have hchild_old_len : left j < a.length :=
        Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length
      have hparent_old_len : j < a.length :=
        Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length
      have hold := hexcept.left_le hij hj hji hl
      rw [← valAt_eq_getElem a hchild_old_len,
        ← valAt_eq_getElem a hparent_old_len] at hold
      have hval :
          valAt (swapAt a i largest) (left j) ≤ valAt (swapAt a i largest) j := by
        rw [hchild_read, hparent_read]
        exact hold
      rw [valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hl hlen_swapped),
        valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
      simpa [largest] using hval
  · intro j hij hj hbad hr
    by_cases hji : j = i
    · subst j
      have hval := valAt_swapAt_i_ge_right
        (a := a) (heapSize := heapSize) (i := i)
        hexcept.heapSize_le_length hi hneq hr
      rw [valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hr hlen_swapped),
        valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
      simpa [largest] using hval
    · have hright_ne_i : right j ≠ i := by
        intro hEq
        unfold right at hEq
        omega
      have hright_ne_largest : right j ≠ largest := by
        intro hEq
        rcases hlargest_child with hleft | hright
        · have : right j = left i := by simpa [hleft] using hEq
          unfold left right at this
          omega
        · have : right j = right i := by simpa [hright] using hEq
          unfold right at this
          omega
      have hchild_read :
          valAt (swapAt a i largest) (right j) = valAt a (right j) :=
        valAt_swapAt_of_ne hi_len hlargest_len hright_ne_i hright_ne_largest
      have hparent_read :
          valAt (swapAt a i largest) j = valAt a j :=
        valAt_swapAt_of_ne hi_len hlargest_len hji hbad
      have hchild_old_len : right j < a.length :=
        Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length
      have hparent_old_len : j < a.length :=
        Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length
      have hold := hexcept.right_le hij hj hji hr
      rw [← valAt_eq_getElem a hchild_old_len,
        ← valAt_eq_getElem a hparent_old_len] at hold
      have hval :
          valAt (swapAt a i largest) (right j) ≤ valAt (swapAt a i largest) j := by
        rw [hchild_read, hparent_read]
        exact hold
      rw [valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hr hlen_swapped),
        valAt_eq_getElem (swapAt a i largest)
          (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
      simpa [largest] using hval

/--
After a nontrivial swap, the new bad node satisfies the path-bound invariant:
its children remain below the value that was moved into its parent.
-/
theorem badChildrenLeParent_after_swap {a : List Nat} {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hstart : start ≤ i) (hi : i < heapSize)
    (hneq : maxChildIndex a heapSize i ≠ i) :
    BadChildrenLeParent
      (swapAt a i (maxChildIndex a heapSize i)) heapSize start
      (maxChildIndex a heapSize i) := by
  let largest := maxChildIndex a heapSize i
  have hdown : i < largest := by
    simpa [largest] using lt_maxChildIndex_of_ne hneq
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hexcept.heapSize_le_length
  have hlargest_len : largest < a.length :=
    Nat.lt_of_lt_of_le hlargest_heap hexcept.heapSize_le_length
  have hparent_largest : parent largest = i := by
    rcases maxChildIndex_eq_left_or_right_of_ne hneq with hleft | hright
    · simpa [largest, hleft] using parent_left i
    · simpa [largest, hright] using parent_right i
  intro _
  constructor
  · intro hl
    have hchild_ne_i : left largest ≠ i := by
      unfold left
      omega
    have hchild_ne_largest : left largest ≠ largest := left_ne_self largest
    have hchild_read :
        valAt (swapAt a i largest) (left largest) = valAt a (left largest) :=
      valAt_swapAt_of_ne hi_len hlargest_len hchild_ne_i hchild_ne_largest
    have hparent_read :
        valAt (swapAt a i largest) (parent largest) = valAt a largest := by
      simpa [hparent_largest] using valAt_swapAt_left hi_len hlargest_len
    have hold := hexcept.left_le (Nat.le_trans hstart (Nat.le_of_lt hdown))
      hlargest_heap (Ne.symm (ne_of_lt hdown)) hl
    rw [← valAt_eq_getElem a
        (Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length),
      ← valAt_eq_getElem a
        (Nat.lt_of_lt_of_le hlargest_heap hexcept.heapSize_le_length)] at hold
    rw [hchild_read, hparent_read]
    exact hold
  · intro hr
    have hchild_ne_i : right largest ≠ i := by
      unfold right
      omega
    have hchild_ne_largest : right largest ≠ largest := right_ne_self largest
    have hchild_read :
        valAt (swapAt a i largest) (right largest) = valAt a (right largest) :=
      valAt_swapAt_of_ne hi_len hlargest_len hchild_ne_i hchild_ne_largest
    have hparent_read :
        valAt (swapAt a i largest) (parent largest) = valAt a largest := by
      simpa [hparent_largest] using valAt_swapAt_left hi_len hlargest_len
    have hold := hexcept.right_le (Nat.le_trans hstart (Nat.le_of_lt hdown))
      hlargest_heap (Ne.symm (ne_of_lt hdown)) hr
    rw [← valAt_eq_getElem a
        (Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length),
      ← valAt_eq_getElem a
        (Nat.lt_of_lt_of_le hlargest_heap hexcept.heapSize_le_length)] at hold
    rw [hchild_read, hparent_read]
    exact hold

/--
Generalized one-swap certificate for recursive heapify.  If the incoming path
edge is protected by {lit}`BadChildrenLeParent`, swapping with the selected
child moves the exception down while preserving all localized obligations from
the original {lit}`start`.
-/
theorem arrayMaxHeapExceptFrom_after_swap_path {a : List Nat}
    {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hstart : start ≤ i) (hi : i < heapSize)
    (hneq : maxChildIndex a heapSize i ≠ i)
    (hbound : BadChildrenLeParent a heapSize start i) :
    ArrayMaxHeapExceptFrom
      (swapAt a i (maxChildIndex a heapSize i)) heapSize start
      (maxChildIndex a heapSize i) := by
  let largest := maxChildIndex a heapSize i
  have hdown : i < largest := by
    simpa [largest] using lt_maxChildIndex_of_ne hneq
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hi_len : i < a.length := Nat.lt_of_lt_of_le hi hexcept.heapSize_le_length
  have hlargest_len : largest < a.length :=
    Nat.lt_of_lt_of_le hlargest_heap hexcept.heapSize_le_length
  have hlen_swapped : heapSize ≤ (swapAt a i largest).length := by
    simpa [largest, swapAt_length] using hexcept.heapSize_le_length
  have hlargest_child : largest = left i ∨ largest = right i := by
    simpa [largest] using maxChildIndex_eq_left_or_right_of_ne hneq
  have hroot :
      ArrayMaxHeapExceptFrom (swapAt a i largest) heapSize i largest :=
    arrayMaxHeapExceptFrom_after_swap_at_root
      (ArrayMaxHeapExceptFrom.mono_start hexcept hstart) hi (by simpa [largest] using hneq)
  refine ⟨hlen_swapped, ?_, ?_⟩
  · intro j hsj hj hbad hl
    by_cases hij : i ≤ j
    · exact hroot.left_le hij hj hbad hl
    · have hji : j < i := Nat.lt_of_not_ge hij
      have hjne_i : j ≠ i := ne_of_lt hji
      by_cases hchild_i : left j = i
      · have hstart_lt_i : start < i := Nat.lt_of_le_of_lt hsj hji
        have hb := hbound hstart_lt_i
        have hlargest_le_parent_i : valAt a largest ≤ valAt a (parent i) := by
          rcases hlargest_child with hleft | hright
          · simpa [largest, hleft] using hb.1 (by simpa [largest, hleft] using hlargest_heap)
          · simpa [largest, hright] using hb.2 (by simpa [largest, hright] using hlargest_heap)
        have hparent_i : parent i = j := by
          rw [← hchild_i]
          exact parent_left j
        have hchild_read :
            valAt (swapAt a i largest) (left j) = valAt a largest := by
          simpa [hchild_i] using valAt_swapAt_left hi_len hlargest_len
        have hparent_read :
            valAt (swapAt a i largest) j = valAt a j :=
          valAt_swapAt_of_ne hi_len hlargest_len hjne_i hbad
        have hval :
            valAt (swapAt a i largest) (left j) ≤
              valAt (swapAt a i largest) j := by
          rw [hchild_read, hparent_read]
          simpa [hparent_i] using hlargest_le_parent_i
        rw [valAt_eq_getElem (swapAt a i largest)
            (Nat.lt_of_lt_of_le hl hlen_swapped),
          valAt_eq_getElem (swapAt a i largest)
            (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
        simpa [largest] using hval
      · by_cases hchild_largest : left j = largest
        · exfalso
          rcases hlargest_child with hleft | hright
          · have : left j = left i := by simpa [largest, hleft] using hchild_largest
            unfold left at this
            omega
          · have : left j = right i := by simpa [largest, hright] using hchild_largest
            unfold left right at this
            omega
        · have hchild_read :
              valAt (swapAt a i largest) (left j) = valAt a (left j) :=
            valAt_swapAt_of_ne hi_len hlargest_len hchild_i hchild_largest
          have hparent_read :
              valAt (swapAt a i largest) j = valAt a j :=
            valAt_swapAt_of_ne hi_len hlargest_len hjne_i hbad
          have hchild_old_len : left j < a.length :=
            Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length
          have hparent_old_len : j < a.length :=
            Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length
          have hold := hexcept.left_le hsj hj hjne_i hl
          rw [← valAt_eq_getElem a hchild_old_len,
            ← valAt_eq_getElem a hparent_old_len] at hold
          have hval :
              valAt (swapAt a i largest) (left j) ≤ valAt (swapAt a i largest) j := by
            rw [hchild_read, hparent_read]
            exact hold
          rw [valAt_eq_getElem (swapAt a i largest)
              (Nat.lt_of_lt_of_le hl hlen_swapped),
            valAt_eq_getElem (swapAt a i largest)
              (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
          simpa [largest] using hval
  · intro j hsj hj hbad hr
    by_cases hij : i ≤ j
    · exact hroot.right_le hij hj hbad hr
    · have hji : j < i := Nat.lt_of_not_ge hij
      have hje_i : j ≠ i := ne_of_lt hji
      by_cases hchild_i : right j = i
      · have hstart_lt_i : start < i := Nat.lt_of_le_of_lt hsj hji
        have hb := hbound hstart_lt_i
        have hlargest_le_parent_i : valAt a largest ≤ valAt a (parent i) := by
          rcases hlargest_child with hleft | hright
          · simpa [largest, hleft] using hb.1 (by simpa [largest, hleft] using hlargest_heap)
          · simpa [largest, hright] using hb.2 (by simpa [largest, hright] using hlargest_heap)
        have hparent_i : parent i = j := by
          rw [← hchild_i]
          exact parent_right j
        have hchild_read :
            valAt (swapAt a i largest) (right j) = valAt a largest := by
          simpa [hchild_i] using valAt_swapAt_left hi_len hlargest_len
        have hparent_read :
            valAt (swapAt a i largest) j = valAt a j :=
          valAt_swapAt_of_ne hi_len hlargest_len hje_i hbad
        have hval :
            valAt (swapAt a i largest) (right j) ≤
              valAt (swapAt a i largest) j := by
          rw [hchild_read, hparent_read]
          simpa [hparent_i] using hlargest_le_parent_i
        rw [valAt_eq_getElem (swapAt a i largest)
            (Nat.lt_of_lt_of_le hr hlen_swapped),
          valAt_eq_getElem (swapAt a i largest)
            (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
        simpa [largest] using hval
      · by_cases hchild_largest : right j = largest
        · exfalso
          rcases hlargest_child with hleft | hright
          · have : right j = left i := by simpa [largest, hleft] using hchild_largest
            unfold left right at this
            omega
          · have : right j = right i := by simpa [largest, hright] using hchild_largest
            unfold right at this
            omega
        · have hchild_read :
              valAt (swapAt a i largest) (right j) = valAt a (right j) :=
            valAt_swapAt_of_ne hi_len hlargest_len hchild_i hchild_largest
          have hparent_read :
              valAt (swapAt a i largest) j = valAt a j :=
            valAt_swapAt_of_ne hi_len hlargest_len hje_i hbad
          have hchild_old_len : right j < a.length :=
            Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length
          have hparent_old_len : j < a.length :=
            Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length
          have hold := hexcept.right_le hsj hj hje_i hr
          rw [← valAt_eq_getElem a hchild_old_len,
            ← valAt_eq_getElem a hparent_old_len] at hold
          have hval :
              valAt (swapAt a i largest) (right j) ≤ valAt (swapAt a i largest) j := by
            rw [hchild_read, hparent_read]
            exact hold
          rw [valAt_eq_getElem (swapAt a i largest)
              (Nat.lt_of_lt_of_le hr hlen_swapped),
            valAt_eq_getElem (swapAt a i largest)
              (Nat.lt_of_lt_of_le hj hlen_swapped)] at hval
          simpa [largest] using hval

/--
Fuelled executable version of {lit}`MAX-HEAPIFY`.  Each recursive call swaps the
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
Fuelled heapify only swaps cells inside the heap prefix.  Therefore every cell
at an index {lit}`k ≥ heapSize` keeps the same value.
-/
theorem maxHeapifyFuel_valAt_of_heapSize_le {fuel : Nat} {a : List Nat}
    {heapSize i k : Nat} (hlen : heapSize ≤ a.length) (hi : i < heapSize)
    (hk : heapSize ≤ k) :
    valAt (maxHeapifyFuel fuel a heapSize i) k = valAt a k := by
  induction fuel generalizing a i with
  | zero =>
      simp [maxHeapifyFuel]
  | succ fuel ih =>
      by_cases hmax : maxChildIndex a heapSize i = i
      · simp [maxHeapifyFuel, hmax]
      · let largest := maxChildIndex a heapSize i
        have hlargest : largest < heapSize := by
          simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
        have hswap_len : heapSize ≤ (swapAt a i largest).length := by
          simpa [largest, swapAt_length] using hlen
        have hswap_read : valAt (swapAt a i largest) k = valAt a k := by
          exact valAt_swapAt_of_ne
            (Nat.lt_of_lt_of_le hi hlen)
            (Nat.lt_of_lt_of_le hlargest hlen)
            (by omega)
            (by omega)
        have hrec := ih (a := swapAt a i largest) (i := largest)
          hswap_len hlargest
        rw [maxHeapifyFuel, if_neg hmax]
        simpa [largest, hswap_read] using hrec

/--
If a {lit}`largerIndex` call returns a target different from its candidate, then the
target must have been the current index.  CLRS uses the same case split when
reasoning about the variable {lit}`largest`.
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
If {lit}`largerIndex` keeps the current index and the candidate is in the heap, then
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
If {lit}`MAX-HEAPIFY` chooses not to swap, the left-child inequality at {lit}`i` holds.
-/
theorem maxChildIndex_eq_self_left_le {a : List Nat} {heapSize i : Nat}
    (hmax : maxChildIndex a heapSize i = i) (hl : left i < heapSize) :
    valAt a (left i) ≤ valAt a i := by
  have hleft : largerIndex a heapSize i (left i) = i :=
    largerIndex_eq_target_forces_current
      (by simpa [maxChildIndex] using hmax) (right_ne_self i)
  exact largerIndex_eq_current_le hleft hl

/--
If {lit}`MAX-HEAPIFY` chooses not to swap, the right-child inequality at {lit}`i` holds.
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
No-swap correctness for {lit}`MAX-HEAPIFY`: if all heap edges except those outgoing
from {lit}`i` are already valid, and {lit}`MAX-HEAPIFY` leaves {lit}`i` in place, the entire
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

/--
Localized no-swap correctness for {lit}`MAX-HEAPIFY`: if all heap edges whose
parents lie in {lit}`start ..< heapSize` are already valid except possibly those
outgoing from {lit}`i`, and {lit}`MAX-HEAPIFY` does not swap at {lit}`i`, then the
localized heap property is fully restored.
-/
theorem arrayMaxHeapFrom_of_exceptFrom_of_maxChildIndex_self {a : List Nat}
    {heapSize start i : Nat} (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hmax : maxChildIndex a heapSize i = i) : ArrayMaxHeapFrom a heapSize start := by
  refine ⟨hexcept.heapSize_le_length, ?_, ?_⟩
  · intro j hstart hj hl
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_left_le hmax hl
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hl hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.left_le hstart hj hji hl
  · intro j hstart hj hr
    by_cases hji : j = i
    · subst j
      have hval := maxChildIndex_eq_self_right_le hmax hr
      rw [valAt_eq_getElem a (Nat.lt_of_lt_of_le hr hexcept.heapSize_le_length),
        valAt_eq_getElem a (Nat.lt_of_lt_of_le hj hexcept.heapSize_le_length)] at hval
      exact hval
    · exact hexcept.right_le hstart hj hji hr

/--
One fuelled {lit}`MAX-HEAPIFY` step is correct once the recursive swap branch has
provided the postcondition for the selected child.  This packages the control
flow of the recursive proof while keeping the deeper path invariant explicit.
-/
theorem arrayMaxHeapFrom_of_maxHeapifyFuel_succ {fuel : Nat} {a : List Nat}
    {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hrec : ∀ _ : maxChildIndex a heapSize i ≠ i,
      ArrayMaxHeapFrom
        (maxHeapifyFuel fuel (swapAt a i (maxChildIndex a heapSize i))
          heapSize (maxChildIndex a heapSize i))
        heapSize start) :
    ArrayMaxHeapFrom (maxHeapifyFuel (fuel + 1) a heapSize i) heapSize start := by
  by_cases hmax : maxChildIndex a heapSize i = i
  · simpa [maxHeapifyFuel, hmax] using
      arrayMaxHeapFrom_of_exceptFrom_of_maxChildIndex_self hexcept hmax
  · simpa [maxHeapifyFuel, hmax] using hrec hmax

/--
Recursive repair theorem for fuelled {lit}`MAX-HEAPIFY`.  The proof follows the
CLRS path argument: each nontrivial swap moves the only local exception to a
strictly larger child index, and {lit}`heapSize - i` is enough fuel for that
strict descent.
-/
theorem arrayMaxHeapFrom_of_maxHeapifyFuel {fuel : Nat} {a : List Nat}
    {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hstart : start ≤ i) (hi : i < heapSize)
    (hbound : BadChildrenLeParent a heapSize start i)
    (hfuel : heapSize - i ≤ fuel) :
    ArrayMaxHeapFrom (maxHeapifyFuel fuel a heapSize i) heapSize start := by
  induction fuel generalizing a start i with
  | zero =>
      omega
  | succ fuel ih =>
      exact arrayMaxHeapFrom_of_maxHeapifyFuel_succ
        (fuel := fuel) (a := a) (heapSize := heapSize) (start := start) (i := i)
        hexcept
        (by
          intro hneq
          let largest := maxChildIndex a heapSize i
          have hstart_largest : start ≤ largest := by
            have hdown : i < largest := by simpa [largest] using lt_maxChildIndex_of_ne hneq
            exact Nat.le_trans hstart (Nat.le_of_lt hdown)
          have hlargest_heap : largest < heapSize := by
            simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
          have hdecrease :
              heapSize - largest < heapSize - i := by
            simpa [largest] using heapSize_sub_maxChildIndex_lt_of_ne
              (a := a) (heapSize := heapSize) (i := i) hi hneq
          have hfuel_child : heapSize - largest ≤ fuel := by
            omega
          exact ih
            (arrayMaxHeapExceptFrom_after_swap_path
              (a := a) (heapSize := heapSize) (start := start) (i := i)
              hexcept hstart hi hneq hbound)
            hstart_largest hlargest_heap
            (badChildrenLeParent_after_swap
              (a := a) (heapSize := heapSize) (start := start) (i := i)
              hexcept hstart hi hneq)
            hfuel_child)

/--
Child-call form of the recursive {lit}`MAX-HEAPIFY` swap branch.  Once
{lit}`largest ≠ i`, the root/child swap moves the unique exception to
{lit}`largest`; enough fuel for that child call repairs the original localized
heap region.
-/
theorem maxHeapifyFuel_child_repair_after_swap {fuel : Nat} {a : List Nat}
    {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hstart : start ≤ i) (hi : i < heapSize)
    (hneq : maxChildIndex a heapSize i ≠ i)
    (hbound : BadChildrenLeParent a heapSize start i)
    (hfuel : heapSize - maxChildIndex a heapSize i ≤ fuel) :
    ArrayMaxHeapFrom
      (maxHeapifyFuel fuel (swapAt a i (maxChildIndex a heapSize i))
        heapSize (maxChildIndex a heapSize i))
      heapSize start := by
  let largest := maxChildIndex a heapSize i
  have hdown : i < largest := by
    simpa [largest] using lt_maxChildIndex_of_ne hneq
  have hstart_largest : start ≤ largest :=
    Nat.le_trans hstart (Nat.le_of_lt hdown)
  have hlargest_heap : largest < heapSize := by
    simpa [largest] using maxChildIndex_lt_heapSize (a := a) (heapSize := heapSize) hi
  have hexcept_child :
      ArrayMaxHeapExceptFrom (swapAt a i largest) heapSize start largest :=
    arrayMaxHeapExceptFrom_after_swap_path
      (a := a) (heapSize := heapSize) (start := start) (i := i)
      hexcept hstart hi hneq hbound
  have hbound_child :
      BadChildrenLeParent (swapAt a i largest) heapSize start largest :=
    badChildrenLeParent_after_swap
      (a := a) (heapSize := heapSize) (start := start) (i := i)
      hexcept hstart hi hneq
  have hrepair :=
    arrayMaxHeapFrom_of_maxHeapifyFuel
      (fuel := fuel) (a := swapAt a i largest) (heapSize := heapSize)
      (start := start) (i := largest)
      hexcept_child hstart_largest hlargest_heap hbound_child
      (by simpa [largest] using hfuel)
  simpa [largest] using hrepair

/--
Named CLRS swap-branch theorem for {lit}`MAX-HEAPIFY`.  If the selected
{lit}`largest` child differs from the current root, then one executable step
performs the root/child swap and the recursive child call repairs the localized
heap.
-/
theorem maxHeapifyFuel_swap_branch_repair {fuel : Nat} {a : List Nat}
    {heapSize start i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize start i)
    (hstart : start ≤ i) (hi : i < heapSize)
    (hneq : maxChildIndex a heapSize i ≠ i)
    (hbound : BadChildrenLeParent a heapSize start i)
    (hfuel : heapSize - maxChildIndex a heapSize i ≤ fuel) :
    ArrayMaxHeapFrom (maxHeapifyFuel (fuel + 1) a heapSize i) heapSize start := by
  have hchild :=
    maxHeapifyFuel_child_repair_after_swap
      (fuel := fuel) (a := a) (heapSize := heapSize) (start := start) (i := i)
      hexcept hstart hi hneq hbound hfuel
  simpa [maxHeapifyFuel, hneq] using hchild

/--
Subtree form of {lit}`MAX-HEAPIFY` correctness: if the localized subtree rooted
at {lit}`i` has at most one bad parent, enough fuel repairs that subtree.
-/
theorem maxHeapifyFuel_repair_subtree {fuel : Nat} {a : List Nat}
    {heapSize i : Nat}
    (hexcept : ArrayMaxHeapExceptFrom a heapSize i i)
    (hi : i < heapSize) (hfuel : heapSize - i ≤ fuel) :
    ArrayMaxHeapFrom (maxHeapifyFuel fuel a heapSize i) heapSize i :=
  arrayMaxHeapFrom_of_maxHeapifyFuel hexcept (Nat.le_refl i) hi
    (BadChildrenLeParent.self a heapSize i) hfuel

/--
Root form of {lit}`MAX-HEAPIFY` correctness: when the only possible bad parent is
the root, enough fuel produces a global max-heap.
-/
theorem maxHeapifyFuel_root_isMaxHeap {fuel : Nat} {a : List Nat}
    {heapSize : Nat} (hexcept : ArrayMaxHeapExcept a heapSize 0)
    (hpos : 0 < heapSize) (hfuel : heapSize ≤ fuel) :
    ArrayMaxHeap (maxHeapifyFuel fuel a heapSize 0) heapSize := by
  have hfrom : ArrayMaxHeapFrom (maxHeapifyFuel fuel a heapSize 0) heapSize 0 :=
    arrayMaxHeapFrom_of_maxHeapifyFuel
      (ArrayMaxHeapExcept.from_start (start := 0) hexcept)
      (Nat.le_refl 0) hpos
      (BadChildrenLeParent.self a heapSize 0)
      (by simpa using hfuel)
  exact ArrayMaxHeapFrom.to_global hfrom

end Chapter06
end CLRS
