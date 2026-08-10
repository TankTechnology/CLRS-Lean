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

Status: `proved` for the functional-list and array-backed models.

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

/-- ENQUEUE: write at the tail and advance the tail (wrapping around); returns
{lit}`none` on overflow when the queue is full. -/
def arrayEnqueue (x : α) (q : ArrayQueue α) : Option (ArrayQueue α) :=
  if q.head = (q.tail + 1) % q.capacity then
    none
  else
    some { store := arrayWrite q.tail x q.store, head := q.head,
           tail := (q.tail + 1) % q.capacity, capacity := q.capacity }

/-- DEQUEUE: read at the head and advance the head (wrapping around); returns
{lit}`none` on underflow when the queue is empty. -/
def arrayDequeue (q : ArrayQueue α) : Option (α × ArrayQueue α) :=
  if q.head = q.tail then
    none
  else
    some (arrayRead q.store q.head,
          { store := q.store, head := (q.head + 1) % q.capacity,
            tail := q.tail, capacity := q.capacity })

/-- Enqueueing into an empty array-backed queue and then dequeueing returns the
enqueued element; the circular wrap leaves the tail one slot ahead of the head. -/
theorem arrayDequeue_arrayEnqueue_empty (x : α) (n : Nat) (f : Nat → α) (hn : 1 < n) :
    (arrayEnqueue x { store := f, head := 0, tail := 0, capacity := n }).bind
        (fun q' => arrayDequeue q') =
      some (x, { store := arrayWrite 0 x f, head := 1 % n, tail := 1 % n, capacity := n }) := by
  unfold arrayEnqueue arrayDequeue
  simp [hn, Nat.mod_eq_of_lt, arrayRead, arrayWrite]

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
    (h : q.head ≠ (q.tail + 1) % q.capacity) :
    (arrayEnqueue x q).map (fun q' => q'.tail) = some ((q.tail + 1) % q.capacity) := by
  simp [arrayEnqueue, h]

end Chapter10
end CLRS
