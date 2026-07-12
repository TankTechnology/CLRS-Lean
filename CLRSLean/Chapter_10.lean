import CLRSLean.Chapter_10.Section_10_1_Stacks_And_Queues
import CLRSLean.Chapter_10.Section_10_2_Linked_Lists
import CLRSLean.Chapter_10.Section_10_4_Rooted_Trees

/-!
# Chapter 10 - Elementary Data Structures

Chapter 10 introduces stacks, queues, linked lists, and rooted-tree
representations.  The current CLRS-Lean pass uses functional lists as the
mathematical model for the first three structures, and a purely functional
tree/forest model for the §10.4 rooted-tree encoding.  This intentionally avoids
pointer mutation while preserving the algebraic claims that the textbook uses
when reasoning about the operations.

## Sections

* 10.1 Stacks and queues: {lit}`proved` for the functional-list model.
  Main results: {lit}`CLRS.Chapter10.pop_push`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_empty`,
  {lit}`CLRS.Chapter10.dequeue_enqueue_nonempty`.
* 10.2 Linked lists: {lit}`proved` for the functional-list model.
  Main results: {lit}`CLRS.Chapter10.listSearch_sound`,
  {lit}`CLRS.Chapter10.mem_listDeleteAll_iff`.
* 10.4 Representing rooted trees: {lit}`proved` for the functional
  rose-tree / left-child-right-sibling model.  Main results: the round-trip
  isomorphism {lit}`CLRS.Chapter10.ofLCRSForest_toLCRSForest` and
  {lit}`CLRS.Chapter10.toLCRSForest_ofLCRSForest` (packaged as the bijection
  {lit}`CLRS.Chapter10.lcrsEquiv`), the single-tree round trip
  {lit}`CLRS.Chapter10.ofLCRS_toLCRS`, and structure preservation
  {lit}`CLRS.Chapter10.toLCRSForest_preorder`.

## Current Gaps

The chapter does not yet formalize pointer-level linked lists or free-list
allocation.  Those belong to a future imperative-memory layer.  Section 10.3
("Implementing pointers and objects") is tracked separately as pure
imperative-memory / allocator work.
-/

namespace CLRS
namespace Chapter10
end Chapter10
end CLRS
