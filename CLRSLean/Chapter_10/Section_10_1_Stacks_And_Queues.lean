import Mathlib

/-!
# CLRS Section 10.1 - Stacks and queues

This section models stacks and queues as functional lists.  The model captures
the textbook algebra of the operations while deferring array bounds, overflow,
underflow exceptions, and pointer mutation to a later RAM-semantics layer.

Main results:

- Theorem {lit}`pop_push`: popping after pushing returns the pushed element and
  the old stack.
- Theorem {lit}`dequeue_enqueue_empty`: enqueueing into an empty queue then
  dequeueing returns that element.
- Theorem {lit}`dequeue_enqueue_nonempty`: enqueueing at the back of a nonempty
  queue does not change the next dequeued front element.

Current gaps:

- None for the functional-list model.  Array-level overflow/underflow and
  circular-buffer proofs are deferred.
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

/-- Pop the top element from a stack, returning `none` on underflow. -/
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

/-- Dequeue the front element, returning `none` on underflow. -/
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

end Chapter10
end CLRS
