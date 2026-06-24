import CLRSLean.Chapter_10.Section_10_1_Stacks_And_Queues
import CLRSLean.Chapter_10.Section_10_2_Linked_Lists

/-!
# Chapter 10 - Elementary Data Structures

Chapter 10 introduces stacks, queues, linked lists, and rooted-tree
representations.  The current CLRSLean pass uses functional lists as the
mathematical model for the first three structures.  This intentionally avoids
pointer mutation while preserving the algebraic claims that the textbook uses
when reasoning about the operations.

## Sections

* 10.1 Stacks and queues: `proved` for the functional-list model.
  Main results: {lit}`CLRS.Chapter10.pop_push`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_empty`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists: `proved` for the functional-list model.
  Main results: {lit}`CLRS.Chapter10.listSearch_sound`,
  {lit}`CLRS.Chapter10.mem_listDeleteAll_iff`.

## Current Gaps

The chapter does not yet formalize pointer-level linked lists, free-list
allocation, or rooted-tree left-child/right-sibling representations.  Those
belong to a future imperative-memory layer.
-/

namespace CLRS
namespace Chapter10
end Chapter10
end CLRS
