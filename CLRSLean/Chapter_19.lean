import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model

/-!
# Chapter 19 - Fibonacci Heaps

Chapter 19 starts with a first-pass abstract Fibonacci-heap model.  The current
Lean surface represents a heap by a finite set of integer keys plus root/mark
counters, proves operation-level set specifications and direct membership
facts plus direct operation-key corollaries for insertion, extract-min,
decrease-key, and deletion, adds old-key preservation corollaries for the
set-updating operations and exact failed membership specifications after heap
operations, direct failed-membership preservation wrappers, exposes direct
operation-result validity wrappers for normalized counters, adds direct minimum
membership/lower-bound wrappers plus
insert/union/extract-min-remaining/decrease-key/delete minimum direct
membership/lower-bound wrappers, direct minimum/extract-min empty-result
wrappers, and positive/empty-result
minimum-after-update specifications,
exposes the standard
potential function with zero-initial and nonnegativity facts, and
packages a conservative degree-bound wrapper for later subtree-size
strengthening, together with a Fibonacci-style lower-bound recurrence,
positivity, adjacent monotonicity, monotonicity, and the first exponential
growth bridge over even and half indices, plus conditional natural-log degree
budget wrappers.  The query surface includes empty-result specifications for
minimum and extract-min.

## Sections

* 19.1 Fibonacci-heap model: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_correct`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_valid`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_minimum_none`,
  {lit}`CLRS.Chapter19.FibHeap.potential_makeHeap`,
  {lit}`CLRS.Chapter19.FibHeap.potential_nonneg`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_le`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.insert_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_valid`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_self`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_inserted`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.union_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_valid`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_of_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_valid`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_valid`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.delete_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_valid`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_of_eq`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.heapPotential_telescope`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_step`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_pos`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_monotone`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_half_le_log_card`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_le_twice_log_card_add_one`, and
  {lit}`CLRS.Chapter19.FibHeap.degree_bound_log`.

## Current Gaps

Pointer-level circular lists, cascading-cut transition systems, consolidation
arrays, and the subtree-size induction leading to the true Fibonacci
log-degree theorem remain strengthening targets.
-/

namespace CLRS
namespace Chapter19
end Chapter19
end CLRS
