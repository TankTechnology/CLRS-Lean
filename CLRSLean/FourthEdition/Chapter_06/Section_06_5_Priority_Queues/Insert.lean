import CLRSLean.FourthEdition.Chapter_06.Section_06_5_Priority_Queues

/-!
# Section 6.5 — Array-level MAX-HEAP-INSERT

This small refinement adds the array operation missing from the existing
priority-queue surface.  Appending a key to a max-heap can invalidate only the
new cell's incoming edge.  The existing upward-exception invariant and bubble
loop therefore provide the complete repair proof.
-/

namespace CLRS
namespace Chapter06

/-- Reading an old array cell is unchanged after appending one new cell. -/
theorem valAt_append_singleton_of_lt {a : List Nat} {key i : Nat}
    (hi : i < a.length) :
    valAt (a ++ [key]) i = valAt a i := by
  simp [valAt, List.getD, List.getElem?_append_left hi]

/--
Appending a key to a full-prefix heap leaves at most the new cell's incoming
edge invalid.  The new cell has no children inside the enlarged heap.
-/
theorem ArrayMaxHeap.append_key_except_up {a : List Nat}
    (hheap : ArrayMaxHeap a a.length) (key : Nat) :
    ArrayMaxHeapExceptUp (a ++ [key]) (a.length + 1) a.length := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro j hj hl hne
    have hchild : left j < a.length := by omega
    have hparent : j < a.length := by
      unfold left at hl
      omega
    rw [valAt_append_singleton_of_lt hchild,
      valAt_append_singleton_of_lt hparent,
      valAt_eq_getElem a hchild,
      valAt_eq_getElem a hparent]
    exact hheap.left_le hparent hchild
  · intro j hj hr hne
    have hchild : right j < a.length := by omega
    have hparent : j < a.length := by
      unfold right at hr
      omega
    rw [valAt_append_singleton_of_lt hchild,
      valAt_append_singleton_of_lt hparent,
      valAt_eq_getElem a hchild,
      valAt_eq_getElem a hparent]
    exact hheap.right_le hparent hchild
  · intro _hpos _hbad
    constructor
    · intro hleft
      unfold left at hleft
      omega
    · intro hright
      unfold right at hright
      omega

/--
Array-level CLRS {lit}`MAX-HEAP-INSERT`: append the new key and bubble it upward.
The fuel is the starting index, matching the existing increase-key repair loop.
-/
def arrayHeapInsert (a : List Nat) (key : Nat) : List Nat :=
  arrayHeapIncreaseKeyBubbleUpFuel a.length (a ++ [key])
    (a.length + 1) a.length

/-- Array-level insertion restores the max-heap invariant. -/
theorem arrayHeapInsert_isMaxHeap {a : List Nat} (key : Nat)
    (hheap : ArrayMaxHeap a a.length) :
    ArrayMaxHeap (arrayHeapInsert a key) (a.length + 1) := by
  exact (hheap.append_key_except_up key).bubbleUpFuel_global
    (by omega) (Nat.le_refl a.length)

/-- Array-level insertion grows the backing list by exactly one cell. -/
theorem arrayHeapInsert_length (a : List Nat) (key : Nat) :
    (arrayHeapInsert a key).length = a.length + 1 := by
  simpa [arrayHeapInsert] using
    arrayHeapIncreaseKeyBubbleUpFuel_length a.length (a ++ [key])
      (a.length + 1) a.length

/-- Array-level insertion adds exactly the new key to the old multiset. -/
theorem arrayHeapInsert_perm (a : List Nat) (key : Nat) :
    (arrayHeapInsert a key).Perm (key :: a) := by
  have hbubble :=
    arrayHeapIncreaseKeyBubbleUpFuel_perm a.length (a ++ [key])
      (a.length + 1) a.length
  have happend : (a ++ [key]).Perm (key :: a) := by
    simpa only [List.singleton_append] using
      (List.perm_append_comm : (a ++ [key]).Perm ([key] ++ a))
  exact hbubble.trans happend

/-- The textbook state package for array-level {lit}`MAX-HEAP-INSERT`. -/
theorem arrayHeapInsert_state_correct {a : List Nat} (key : Nat)
    (hheap : ArrayMaxHeap a a.length) :
    ArrayMaxHeap (arrayHeapInsert a key) (a.length + 1) ∧
      (arrayHeapInsert a key).length = a.length + 1 ∧
      (arrayHeapInsert a key).Perm (key :: a) := by
  exact ⟨arrayHeapInsert_isMaxHeap key hheap,
    arrayHeapInsert_length a key, arrayHeapInsert_perm a key⟩

end Chapter06
end CLRS
