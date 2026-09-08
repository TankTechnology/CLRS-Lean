import CLRSLean.FourthEdition.Chapter_10
open CLRS.Chapter10
#check ArrayStack.Valid
#check ArrayStack.empty_valid
#check ArrayQueue.Valid
#check ArrayQueue.empty_valid
#check arrayPush_preserves_valid
#check arrayPop_preserves_valid
#check arrayEnqueue_preserves_valid
#check arrayDequeue_preserves_valid
#check listSearch_eq_none_iff
#check listSearch_eq_some_iff_prefix
#check listSearch_eq_some_iff_firstIndex

-- Capacity zero is legal for an empty stack, which rejects both operations.
example : (ArrayStack.empty 0 (fun _ => (0 : Nat))).Valid := ArrayStack.empty_valid _ _
example : arrayPush 7 (ArrayStack.empty 0 (fun _ => (0 : Nat))) = none := by
  simp [arrayPush, ArrayStack.empty]
example : arrayPop (ArrayStack.empty 0 (fun _ => (0 : Nat))) = none := by
  simp [arrayPop, ArrayStack.empty]

-- The previously accepted zero-capacity enqueue is now rejected.
example : arrayEnqueue 7 (ArrayQueue.empty 0 (fun _ => (0 : Nat))) = none := by
  simp [arrayEnqueue, ArrayQueue.Valid, ArrayQueue.empty]
example : arrayDequeue (ArrayQueue.empty 0 (fun _ => (0 : Nat))) = none := by
  simp [arrayDequeue, ArrayQueue.Valid, ArrayQueue.empty]

-- Invalid pointer states are rejected before reading or writing the store.
example : arrayEnqueue 7
    ({ store := fun _ => 0, head := 4, tail := 0, capacity := 4 } : ArrayQueue Nat) = none := by
  simp [arrayEnqueue, ArrayQueue.Valid]
example : arrayDequeue
    ({ store := fun _ => 0, head := 0, tail := 4, capacity := 4 } : ArrayQueue Nat) = none := by
  simp [arrayDequeue, ArrayQueue.Valid]
example : arrayDequeue
    ({ store := fun _ => 0, head := 1, tail := 0, capacity := 0 } : ArrayQueue Nat) = none := by
  simp [arrayDequeue, ArrayQueue.Valid]

-- Capacity one is valid but its reserved slot leaves no enqueue space.
example : (ArrayQueue.empty 1 (fun _ => (0 : Nat))).Valid :=
  ArrayQueue.empty_valid _ _ (by decide)
example : arrayEnqueue 7 (ArrayQueue.empty 1 (fun _ => (0 : Nat))) = none := by
  simp [arrayEnqueue, ArrayQueue.Valid, ArrayQueue.empty]

-- Tail and head wrap independently at the capacity boundary.
example : (arrayEnqueue 7
    ({ store := fun _ => 0, head := 1, tail := 3, capacity := 4 } : ArrayQueue Nat)).map
      (fun q => q.tail) = some 0 := by decide
example : (arrayDequeue
    ({ store := id, head := 3, tail := 1, capacity := 4 } : ArrayQueue Nat)).map
      (fun result => (result.1, result.2.head)) = some (3, 0) := by decide

-- A concrete interleaved trace exercises wraparound and preserves arrival order.
example : (do
    let q₁ ← arrayEnqueue 10 (ArrayQueue.empty 3 (fun _ => (0 : Nat)))
    let q₂ ← arrayEnqueue 20 q₁
    let (x, q₃) ← arrayDequeue q₂
    let q₄ ← arrayEnqueue 30 q₃
    let (y, q₅) ← arrayDequeue q₄
    let (z, _) ← arrayDequeue q₅
    pure (x, y, z) : Option (Nat × Nat × Nat)) = some (10, 20, 30) := by decide

-- Search returns the first matching payload, not a later equal-key payload.
example : listSearch (fun x : Nat × String => x.1 == 2)
    [(1, "skip"), (2, "first"), (2, "second")] = some (2, "first") := by decide
example : listSearch (fun n : Nat => n == 9) [1, 2, 3] = none := by decide
example (p : α → Bool) (xs : List α) (x : α) (h : listSearch p xs = some x) :
    ∃ (i : Nat) (hi : i < xs.length), xs[i] = x ∧
      ∀ j (hj : j < i), p (xs[j]'(Nat.lt_trans hj hi)) = false :=
  ((listSearch_eq_some_iff_firstIndex p xs x).mp h).2

-- Delete-all deliberately removes every equal value.
example [DecidableEq α] (x : α) : listDeleteAll x [x, x] = [] := by simp [listDeleteAll]
