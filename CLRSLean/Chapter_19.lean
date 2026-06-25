import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model

/-!
# Chapter 19 - Fibonacci Heaps

Chapter 19 starts with a first-pass abstract Fibonacci-heap model.  The current
Lean surface represents a heap by a finite set of integer keys plus root/mark
counters, proves operation-level set specifications and direct membership
facts for insertion, union, extract-min, decrease-key, and deletion, exposes
the standard potential function with zero-initial and nonnegativity facts, and
packages a conservative degree-bound wrapper for later subtree-size
strengthening, together with a Fibonacci-style lower-bound recurrence,
positivity, adjacent monotonicity, monotonicity, and the first exponential
growth bridge over even and half indices.  The query surface includes empty-result
specifications for minimum and extract-min.

## Sections

* 19.1 Fibonacci-heap model: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_correct`,
  {lit}`CLRS.Chapter19.FibHeap.potential_makeHeap`,
  {lit}`CLRS.Chapter19.FibHeap.potential_nonneg`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.heapPotential_telescope`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_step`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_pos`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_monotone`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`, and
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
