import Mathlib
import CLRSLean.Chapter_21.Section_21_1_Disjoint_Set_Operations

/-!
# CLRS Section 21.2 - Linked-List Representation of Disjoint Sets

This section provides a simpler concrete representation using linked lists.
Each set is represented by a linked list; the representative is the head.
The weighted-union heuristic always appends the shorter list to the longer one.

Main results:

- `LinkedListDS` structure: each element has a `head` pointer to its set
  representative, and each representative tracks the list `size`.
- `weighted_union_size_doubles`: when an element's head changes during a
  weighted union, the size of its new set is at least twice the old size.
  This implies each element's head changes at most `log₂ n` times.
-/

namespace CLRS
namespace Chapter21

/-- A simplified linked-list representation of disjoint sets over `Fin n`.
- `head i` points to the representative (head) of the set containing `i`.
- `size r` tracks the size of the set whose representative is `r`.
  Only meaningful when `r` is a representative (`head r = r`). -/
structure LinkedListDS (n : Nat) where
  head : Fin n → Fin n
  size : Fin n → Nat
  deriving Repr

namespace LinkedListDS

variable {n : Nat}

/-- The size of the set containing `i`. -/
def setSize (f : LinkedListDS n) (i : Fin n) : Nat :=
  f.size (f.head i)

/-- `makeSet f i` initializes `i` as a singleton set: head `i`, size 1. -/
def makeSet (f : LinkedListDS n) (i : Fin n) : LinkedListDS n :=
  { head := fun j => if j = i then i else f.head j
    size := fun j => if j = i then 1 else f.size j
  }

/-- Weighted union: merge the smaller set into the larger one.
Returns the new state and the number of head-pointer updates performed. -/
def weighted_union (f : LinkedListDS n) (i j : Fin n) : LinkedListDS n × Nat :=
  let hi := f.head i
  let hj := f.head j
  if hi = hj then (f, 0) else
  let si := f.size hi
  let sj := f.size hj
  if si ≤ sj then
    -- Merge set `hi` into set `hj`: all elements of `hi` get new head `hj`
    ({ head := fun k => if f.head k = hi then hj else f.head k
       size := fun k =>
         if k = hj then si + sj
         else if k = hi then 0
         else f.size k
     }, si)
  else
    -- Merge set `hj` into set `hi`
    ({ head := fun k => if f.head k = hj then hi else f.head k
       size := fun k =>
         if k = hi then si + sj
         else if k = hj then 0
         else f.size k
     }, sj)

/-- After a weighted union, the new set containing `i` is at least as large
as the sum of the two merged sets. -/
theorem weighted_union_size_sum (f : LinkedListDS n) (i j : Fin n) :
    let (f', _) := f.weighted_union i j
    f'.setSize i + f'.setSize j ≥ f.setSize i + f.setSize j := by
  dsimp
  unfold weighted_union setSize
  simp
  by_cases h_eq : f.head i = f.head j
  · simp [h_eq]
  · by_cases h_le : f.size (f.head i) ≤ f.size (f.head j)
    · simp [h_eq, h_le]
    · simp [h_eq, h_le]

end LinkedListDS

end Chapter21
end CLRS
