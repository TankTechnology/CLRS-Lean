import Mathlib

/-!
# CLRS Section 10.1 - Stacks and queues

This section models stacks and queues both as functional lists and, matching the
fourth-edition §10.1 "simple array-based data structures" interface, as
array-backed stacks and queues with a top/head/tail pointer, overflow and
underflow handling, and circular wrap-around.  The list model captures the
textbook algebra; the array model captures the bounded-storage reading while
still deferring a concrete RAM execution layer.

Main results:

- Theorem {lit}`pop_push`: popping after pushing returns the pushed element and
  the old stack.
- Theorem {lit}`dequeue_enqueue_empty`: enqueueing into an empty queue then
  dequeueing returns that element.
- Theorem {lit}`dequeue_enqueue_nonempty`: enqueueing at the back of a nonempty
  queue does not change the next dequeued front element.
- Theorem {lit}`arrayPop_arrayPush`: popping immediately after pushing an
  array-backed stack returns the pushed element and restores the top pointer.
- Theorem {lit}`arrayDequeue_arrayEnqueue_empty`: enqueueing into an empty
  array-backed circular queue and then dequeueing returns the enqueued element.
- Theorem {lit}`arrayPush_overflow` / {lit}`arrayPop_empty` /
  {lit}`arrayEnqueue_overflow` / {lit}`arrayDequeue_empty`: array overflow and
  underflow are reported as {lit}`none`.

Status: {lit}`proved` for functional-list LIFO/FIFO, valid array-pointer
transitions, and the stated local array round trips. A general circular-array
FIFO abstraction theorem is not claimed here.

Deferred refinements: RAM execution, pointer mutation, and memory costs.
-/

namespace CLRS
namespace Chapter10

/-! ## Stacks -/

/-- A functional stack is a list whose head is the stack top. -/
abbrev Stack (α : Type u) := List α

/-- The empty stack. -/
def emptyStack : Stack α :=
  []

/-- Push an element onto the top of a stack. -/
def push (x : α) (s : Stack α) : Stack α :=
  x :: s

/-- Pop the top element from a stack, returning {lit}`none` on underflow. -/
def pop : Stack α → Option (α × Stack α)
  | [] => none
  | x :: xs => some (x, xs)

/-- Popping immediately after pushing recovers the pushed element and old stack. -/
theorem pop_push (x : α) (s : Stack α) :
    pop (push x s) = some (x, s) := by
  rfl

/-- Popping the empty stack reports underflow. -/
theorem pop_empty : pop (emptyStack : Stack α) = none := by
  rfl

/-- Pushing increases stack length by one. -/
theorem length_push (x : α) (s : Stack α) :
    (push x s).length = s.length + 1 := by
  simp [push]

/-! ## Queues -/

/-- A functional queue is a list whose head is the dequeue front. -/
abbrev Queue (α : Type u) := List α

/-- The empty queue. -/
def emptyQueue : Queue α :=
  []

/-- Enqueue an element at the back of the queue. -/
def enqueue (x : α) (q : Queue α) : Queue α :=
  q ++ [x]

/-- Dequeue the front element, returning {lit}`none` on underflow. -/
def dequeue : Queue α → Option (α × Queue α)
  | [] => none
  | x :: xs => some (x, xs)

/-- Dequeueing the empty queue reports underflow. -/
theorem dequeue_empty : dequeue (emptyQueue : Queue α) = none := by
  rfl

/-- Enqueueing into an empty queue and then dequeueing returns that element. -/
theorem dequeue_enqueue_empty (x : α) :
    dequeue (enqueue x emptyQueue) = some (x, emptyQueue) := by
  rfl

/--
If a queue is already nonempty, enqueueing at the back does not change the next
front element to be dequeued.
-/
theorem dequeue_enqueue_nonempty (front x : α) (rest : List α) :
    dequeue (enqueue x (front :: rest)) = some (front, rest ++ [x]) := by
  rfl

/-- Enqueueing increases queue length by one. -/
theorem length_enqueue (x : α) (q : Queue α) :
    (enqueue x q).length = q.length + 1 := by
  simp [enqueue]

/-! ## Array-backed stacks and queues -/

/-- A bounded array is modeled as a total indexed function; unwritten slots take a
junk value.  This is the functional interface of the fourth-edition §10.1 array,
deferring RAM storage to a later execution model. -/
abbrev ArrayStore (α : Type u) := Nat → α

/-- Read the element stored at index {lit}`i` of an array. -/
def arrayRead (A : ArrayStore α) (i : Nat) : α := A i

/-- Write {lit}`x` at index {lit}`i`, leaving every other index unchanged. -/
def arrayWrite (i : Nat) (x : α) (A : ArrayStore α) : ArrayStore α :=
  Function.update A i x

/-- Reading immediately after writing returns the written value. -/
theorem arrayRead_arrayWrite_same (i : Nat) (x : α) (A : ArrayStore α) :
    arrayRead (arrayWrite i x A) i = x := by
  simp [arrayRead, arrayWrite]

/-- Writing at one index leaves every other index unchanged. -/
theorem arrayRead_arrayWrite_other {i j : Nat} (h : j ≠ i) (x : α) (A : ArrayStore α) :
    arrayRead (arrayWrite i x A) j = arrayRead A j := by
  simp [arrayRead, arrayWrite, h]

/-- An array-backed stack of capacity {lit}`n`: a store together with a top
pointer and its capacity bound.  Elements occupy slots `0..top-1` with the stack
top at index `top-1` (CLRS §10.1). -/
structure ArrayStack (α : Type u) where
  store : ArrayStore α
  top : Nat
  capacity : Nat

/-- Legal raw stack state: occupied slots fit within the capacity. Zero-capacity
stacks are valid exactly when empty. -/
def ArrayStack.Valid (s : ArrayStack α) : Prop := s.top ≤ s.capacity

/-- Construct an empty stack over any supplied backing store. -/
def ArrayStack.empty (capacity : Nat) (store : ArrayStore α) : ArrayStack α :=
  ⟨store, 0, capacity⟩

/-- Every empty stack satisfies its pointer bound, including capacity zero. -/
theorem ArrayStack.empty_valid (capacity : Nat) (store : ArrayStore α) :
    (ArrayStack.empty capacity store).Valid := Nat.zero_le _

/-- PUSH onto an array-backed stack: write at the current top and advance the top
pointer; returns {lit}`none` on overflow when the stack is already full. -/
def arrayPush (x : α) (s : ArrayStack α) : Option (ArrayStack α) :=
  if s.top < s.capacity then
    some { store := arrayWrite s.top x s.store, top := s.top + 1, capacity := s.capacity }
  else
    none

/-- POP from an array-backed stack: return the top element and the stack with the
top pointer lowered; returns {lit}`none` on underflow when the stack is empty. -/
def arrayPop (s : ArrayStack α) : Option (α × ArrayStack α) :=
  if s.top = 0 then
    none
  else
    let t := s.top - 1
    some (arrayRead s.store t, { store := s.store, top := t, capacity := s.capacity })

/-- Popping immediately after pushing (on a non-full stack) returns the pushed
element and restores the top pointer; the freed slot keeps its value. -/
theorem arrayPop_arrayPush (x : α) (s : ArrayStack α) (h : s.top < s.capacity) :
    (arrayPush x s).bind (fun s' => arrayPop s') =
      some (x, { store := arrayWrite s.top x s.store, top := s.top, capacity := s.capacity }) := by
  unfold arrayPush arrayPop
  simp [h, arrayRead, arrayWrite]

/-- Popping an empty array-backed stack reports underflow. -/
theorem arrayPop_empty (f : Nat → α) (n : Nat) :
    arrayPop ({ store := f, top := 0, capacity := n } : ArrayStack α) = none := by
  simp [arrayPop]

/-- Pushing onto a full array-backed stack reports overflow. -/
theorem arrayPush_overflow (x : α) (s : ArrayStack α) (h : s.top = s.capacity) :
    arrayPush x s = none := by
  simp [arrayPush, h]

/-- An array-backed circular queue of capacity {lit}`n`: a store with `head` and
`tail` pointers (CLRS §10.1).  Following the textbook, the array holds at most
`n-1` elements: the queue is empty when `head = tail` and full when
`head = (tail + 1) mod n`, with indices wrapping around. -/
structure ArrayQueue (α : Type u) where
  store : ArrayStore α
  head : Nat
  tail : Nat
  capacity : Nat

/-- Legal circular-queue state. One slot is reserved to distinguish full from
empty, so a valid capacity-one queue has no usable storage slots. -/
def ArrayQueue.Valid (q : ArrayQueue α) : Prop :=
  0 < q.capacity ∧ q.head < q.capacity ∧ q.tail < q.capacity

instance (q : ArrayQueue α) : Decidable q.Valid :=
  inferInstanceAs (Decidable (0 < q.capacity ∧ q.head < q.capacity ∧ q.tail < q.capacity))

/-- Construct an empty raw queue; positive capacity makes it valid. -/
def ArrayQueue.empty (capacity : Nat) (store : ArrayStore α) : ArrayQueue α :=
  ⟨store, 0, 0, capacity⟩

/-- Empty circular queues are valid precisely for positive capacity. -/
theorem ArrayQueue.empty_valid (capacity : Nat) (store : ArrayStore α)
    (hcapacity : 0 < capacity) : (ArrayQueue.empty capacity store).Valid :=
  ⟨hcapacity, hcapacity, hcapacity⟩

/-- ENQUEUE: write at the tail and advance the tail (wrapping around); returns
{lit}`none` on overflow or an invalid raw state, including zero capacity. -/
def arrayEnqueue (x : α) (q : ArrayQueue α) : Option (ArrayQueue α) :=
  if q.Valid then
    if q.head = (q.tail + 1) % q.capacity then
      none
    else
      some { store := arrayWrite q.tail x q.store, head := q.head,
             tail := (q.tail + 1) % q.capacity, capacity := q.capacity }
  else none

/-- DEQUEUE: read at the head and advance the head (wrapping around); returns
{lit}`none` on underflow or an invalid raw state. -/
def arrayDequeue (q : ArrayQueue α) : Option (α × ArrayQueue α) :=
  if q.Valid then
    if q.head = q.tail then
      none
    else
      some (arrayRead q.store q.head,
            { store := q.store, head := (q.head + 1) % q.capacity,
              tail := q.tail, capacity := q.capacity })
  else none

/-- Enqueueing into an empty array-backed queue and then dequeueing returns the
enqueued element; the resulting head and tail are equal again after the dequeue. -/
theorem arrayDequeue_arrayEnqueue_empty (x : α) (n : Nat) (f : Nat → α) (hn : 1 < n) :
    (arrayEnqueue x { store := f, head := 0, tail := 0, capacity := n }).bind
        (fun q' => arrayDequeue q') =
      some (x, { store := arrayWrite 0 x f, head := 1 % n, tail := 1 % n, capacity := n }) := by
  unfold arrayEnqueue arrayDequeue
  simp [ArrayQueue.Valid, hn, show 0 < n by omega, Nat.mod_eq_of_lt, arrayRead, arrayWrite]

/-- Dequeueing an empty array-backed queue reports underflow. -/
theorem arrayDequeue_empty (f : Nat → α) (n : Nat) :
    arrayDequeue ({ store := f, head := 0, tail := 0, capacity := n } : ArrayQueue α) = none := by
  simp [arrayDequeue]

/-- Enqueueing into a full array-backed queue reports overflow. -/
theorem arrayEnqueue_overflow (x : α) (q : ArrayQueue α)
    (h : q.head = (q.tail + 1) % q.capacity) :
    arrayEnqueue x q = none := by
  simp [arrayEnqueue, h]

/-- Enqueueing advances the tail pointer, wrapping modulo the capacity. -/
theorem arrayEnqueue_tail_wraps (x : α) (q : ArrayQueue α)
    (hq : q.Valid) (h : q.head ≠ (q.tail + 1) % q.capacity) :
    (arrayEnqueue x q).map (fun q' => q'.tail) = some ((q.tail + 1) % q.capacity) := by
  simp [arrayEnqueue, hq, h]


/-! ## Validity and safe raw-state handling -/

/-- A successful push stays within capacity and preserves that capacity. -/
theorem arrayPush_preserves_valid {x : α} {s s' : ArrayStack α}
    (h : arrayPush x s = some s') : s'.Valid ∧ s'.capacity = s.capacity := by
  unfold arrayPush at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    constructor
    · dsimp [ArrayStack.Valid]
      omega
    · rfl
  · simp at h

/-- Popping a valid stack preserves validity and capacity. -/
theorem arrayPop_preserves_valid {s s' : ArrayStack α} {x : α}
    (hs : s.Valid) (h : arrayPop s = some (x, s')) :
    s'.Valid ∧ s'.capacity = s.capacity := by
  unfold arrayPop at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    dsimp [ArrayStack.Valid] at hs ⊢
    omega

/-- Invalid raw queues cannot accept an element. -/
theorem arrayEnqueue_invalid (x : α) (q : ArrayQueue α) (hq : ¬ q.Valid) :
    arrayEnqueue x q = none := by simp [arrayEnqueue, hq]

/-- Invalid raw queues cannot produce an element. -/
theorem arrayDequeue_invalid (q : ArrayQueue α) (hq : ¬ q.Valid) :
    arrayDequeue q = none := by simp [arrayDequeue, hq]

/-- Zero-capacity queues reject every enqueue, independently of pointer values. -/
theorem arrayEnqueue_zero_capacity (x : α) (q : ArrayQueue α) (h : q.capacity = 0) :
    arrayEnqueue x q = none :=
  arrayEnqueue_invalid x q (by simp [ArrayQueue.Valid, h])

/-- Zero-capacity queues reject every dequeue, independently of pointer values. -/
theorem arrayDequeue_zero_capacity (q : ArrayQueue α) (h : q.capacity = 0) :
    arrayDequeue q = none :=
  arrayDequeue_invalid q (by simp [ArrayQueue.Valid, h])

/-- Successful enqueue preserves legal pointers and the capacity. The validity
check also guarantees that its write occurs at an in-range tail index. -/
theorem arrayEnqueue_preserves_valid {x : α} {q q' : ArrayQueue α}
    (h : arrayEnqueue x q = some q') : q'.Valid ∧ q'.capacity = q.capacity := by
  unfold arrayEnqueue at h
  split at h
  next hq =>
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst q'
      exact ⟨⟨hq.1, hq.2.1, Nat.mod_lt _ hq.1⟩, rfl⟩
  · simp at h

/-- Successful dequeue preserves legal pointers and the capacity. -/
theorem arrayDequeue_preserves_valid {q q' : ArrayQueue α} {x : α}
    (h : arrayDequeue q = some (x, q')) : q'.Valid ∧ q'.capacity = q.capacity := by
  unfold arrayDequeue at h
  split at h
  next hq =>
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact ⟨⟨hq.1, Nat.mod_lt _ hq.1, hq.2.2⟩, rfl⟩
  · simp at h

/-- Every successful enqueue uses a valid input state and an in-range write. -/
theorem arrayEnqueue_valid_input {x : α} {q q' : ArrayQueue α}
    (h : arrayEnqueue x q = some q') : q.Valid := by
  by_contra hq
  simp [arrayEnqueue, hq] at h

/-- Every successful dequeue reads a valid input state. -/
theorem arrayDequeue_valid_input {q q' : ArrayQueue α} {x : α}
    (h : arrayDequeue q = some (x, q')) : q.Valid := by
  by_contra hq
  simp [arrayDequeue, hq] at h

end Chapter10
end CLRS
